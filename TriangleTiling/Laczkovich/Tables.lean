/-
Laczkovich's classification of congruent tilings of a triangle, in the form tabulated in Beeson,
*No triangle can be cut into seven congruent triangles* (arXiv:1811.09723):

* Table `laczkovich` (all angles of the tile commensurable with `π`): `table_commensurable`;
* Table `laczkovich2` (not all angles commensurable with `π`): `table_incommensurable`.

Both are derived from M. Bonfioli's Lean formalization (package `Erdos634`, repository
`formalizing-triangle-tiling-in-lean`; all of it marked NOTE/UNAUDITED there):

* Table `laczkovich` from `LaczFormal.classify_total`: Laczkovich, Discrete Math. 140 (1995),
  Thms 5.1 and 5.3, with the three equilateral sporadic rows removed by Laczkovich, DCG 48 (2012),
  Thm 3.3; for congruent tiles.
* Table `laczkovich2` from `LemmaCFinal.lemmaC_general` and `LemmaPProof.lemmaP_general`:
  Laczkovich (1995), Thm 4.1, with the target shapes of his Thms 2.4 and 2.5; for congruent tiles.

Conventions (Bonfioli's): `D.model.angleAt k` is the tile's angle at its vertex `k`,
`D.target.angleAt k` the angle of `ABC` at its vertex `k`; `TileAngles D x y z` and
`TgtAngles D x y z` say that the tile's (resp. `ABC`'s) angles are `x, y, z` in some order;
`SimilarTM D` says that `ABC` is similar to the tile; `IrrPi x` says that `x` is not a rational
multiple of `π`.
-/
import Erdos634.Draft.LaczFormalUnifC
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.LemmaPProof

namespace TriangleTiling.Laczkovich

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)

variable {N : ℕ} (D : CongruentDissection N)

/-! ### The rows -/

/-- Row "`γ = π/2`, `ABC = (α, α, 2β)`": the tile has angles `α, β, π/2` and `ABC` has angles
`α, α, 2β`. -/
def RightRow : Prop :=
  ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D α α (2 * β)

/-- Row "`ABC` equilateral, tile `(π/6, π/6, 2π/3)`". -/
def EquiRow : Prop :=
  TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) ∧ Equilateral D

/-! ### Angle triples -/

theorem fin3_third : ∀ p q : Fin 3, p ≠ q → ∃ r, r ≠ p ∧ r ≠ q := by decide

/-- A triangle's angles at three distinct vertices add up to `π`. -/
theorem angleAt_sum3 (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    T.angleAt p + T.angleAt q + T.angleAt r = Real.pi := by
  rw [Erdos634.Draft.LemmaCFinal.sum3 T.angleAt p q r hpq hpr hqr]
  exact T.angleAt_sum

/-- The angles of a triangle at three distinct vertices, as an unordered triple. -/
theorem triple_of (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ σ : Equiv.Perm (Fin 3), T.angleAt (σ 0) = T.angleAt p ∧ T.angleAt (σ 1) = T.angleAt q ∧
      T.angleAt (σ 2) = T.angleAt r := by
  refine ⟨Erdos634.Draft.LemmaCFinal.permOf p q r hpq hpr hqr, ?_, ?_, ?_⟩
  · rw [Erdos634.Draft.LemmaCFinal.permOf_0]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_1]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_2]

/-- Two equal angles `x` of `ABC`: its angles are `x, x, π - 2x`. -/
theorem tgt_of_two {i j : Fin 3} (hij : i ≠ j) {x : ℝ} (hi : D.target.angleAt i = x)
    (hj : D.target.angleAt j = x) : TgtAngles D x x (Real.pi - 2 * x) := by
  obtain ⟨r, hri, hrj⟩ := fin3_third i j hij
  have hs := angleAt_sum3 D.target hij hri.symm hrj.symm
  obtain ⟨σ, h0, h1, h2⟩ := triple_of D.target hij hri.symm hrj.symm
  exact ⟨σ, h0.trans hi, h1.trans hj, by rw [h2]; linarith⟩

/-- The right-angle row, from a right angle at `k` and two angles of `ABC` equal to the tile's
angle at `l ≠ k`. -/
theorem rightRow_of {k l : Fin 3} (hlk : l ≠ k) (hk : D.model.angleAt k = Real.pi / 2)
    {j₁ j₂ : Fin 3} (hj : j₁ ≠ j₂) (h1 : D.target.angleAt j₁ = D.model.angleAt l)
    (h2 : D.target.angleAt j₂ = D.model.angleAt l) : RightRow D := by
  obtain ⟨m, hml, hmk⟩ := fin3_third l k hlk
  have hs := angleAt_sum3 D.model hml.symm hlk hmk
  obtain ⟨σ, h0, h1', h2'⟩ := triple_of D.model hml.symm hlk hmk
  refine ⟨D.model.angleAt l, D.model.angleAt m, ⟨σ, h0, h1', h2'.trans hk⟩, ?_⟩
  obtain ⟨τ, t0, t1, t2⟩ := tgt_of_two D hj h1 h2
  exact ⟨τ, t0, t1, by rw [t2]; linarith⟩

theorem tileAngles_of_eq {x y z x' y' z' : ℝ} (h : TileAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TileAngles D x' y' z' := by
  subst hx hy hz; exact h

theorem tgtAngles_of_eq {x y z x' y' z' : ℝ} (h : TgtAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx hy hz; exact h

/-- All three angles of `ABC` equal `π/3`: `ABC` is equilateral. -/
theorem equilateral_of (h : TgtAngles D (Real.pi / 3) (Real.pi / 3) (Real.pi / 3)) :
    Equilateral D := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  intro k
  have hk : k = σ (σ.symm k) := (σ.apply_symm_apply k).symm
  have : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases this (σ.symm k) with h | h | h <;> rw [hk, h] <;> assumption

/-- Angles commensurable with `π` are rational multiples of `π / n` for one `n`. -/
theorem rational_angles_nat (T : Tri) (h : ∀ k, ∃ q : ℚ, T.angleAt k = q * Real.pi) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin 3 → ℕ, ∀ k, T.angleAt k = a k * Real.pi / n := by
  choose q hq using h
  set n := (q 0).den * (q 1).den * (q 2).den with hndef
  have hn : 0 < n := by positivity
  have hdvd : ∀ k, (q k).den ∣ n := by
    intro k; fin_cases k
    · exact ⟨(q 1).den * (q 2).den, by simp [n]; ring⟩
    · exact ⟨(q 0).den * (q 2).den, by simp [n]; ring⟩
    · exact ⟨(q 0).den * (q 1).den, by simp [n]; ring⟩
  have hpos : ∀ k, 0 < q k := by
    intro k
    have h1 := Erdos634.Geometry.CaseA.LemmaV.angle_pos T k
    rw [hq k] at h1
    have : (0 : ℝ) < q k := pos_of_mul_pos_left h1 Real.pi_pos.le
    exact_mod_cast this
  have hint : ∀ k, ∃ m : ℕ, (m : ℚ) = q k * n := by
    intro k
    obtain ⟨m', hm'⟩ := hdvd k
    refine ⟨(q k).num.toNat * m', ?_⟩
    have h1 : ((q k).num.toNat : ℚ) = (q k).num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr (hpos k)).le
    push_cast
    rw [h1, hm']
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  choose a ha using hint
  refine ⟨n, hn, a, fun k => ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hak : (a k : ℝ) = (q k : ℝ) * n := by exact_mod_cast ha k
  rw [hq k, hak]
  field_simp

/-! ### Table `laczkovich`: commensurable angles -/

/-- **Table `laczkovich`** (NoSeven paper; Laczkovich 1995 Thms 5.1, 5.3 and 2012 Thm 3.3, for
congruent tiles). If the triangle `ABC` is tiled by congruent copies of a tile all of whose angles
are rational multiples of `π`, then either `ABC` is similar to the tile, or the tile has angles
`(α, β, π/2)` and `ABC` has angles `(α, α, 2β)`, or `ABC` is equilateral and the tile has angles
`(π/6, π/6, 2π/3)`. -/
theorem table_commensurable (hrat : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi) :
    SimilarTM D ∨ RightRow D ∨ EquiRow D := by
  obtain ⟨n, hn, a, ha⟩ := rational_angles_nat D.model hrat
  obtain ⟨n', hn', a', hgcd, ha'⟩ := Erdos634.CaseA.R0c.exists_primitive D.model hn a ha
  rcases Erdos634.Draft.LaczFormal.classify_total D hn' a' ha' hgcd with
    h | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (rightRow_of D hlk hk hj h1 h2))
  · rcases h with ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
    · -- `(π/6, π/6, 2π/3)` on the equilateral triangle.
      refine Or.inr (Or.inr ⟨tileAngles_of_eq D hT (by ring) (by ring) (by ring), ?_⟩)
      exact equilateral_of D (tgtAngles_of_eq D hG (by ring) (by ring) (by ring))
    · -- `(π/6, π/3, π/2)` on `(π/6, π/6, 2π/3)`: the right-angle row with `α = π/6`.
      exact Or.inr (Or.inl ⟨Real.pi / 6, Real.pi / 3,
        tileAngles_of_eq D hT (by ring) (by ring) (by ring),
        tgtAngles_of_eq D hG (by ring) (by ring) (by ring)⟩)
    · -- `(π/6, π/3, π/2)` on the equilateral triangle: the right-angle row with `α = π/3`.
      exact Or.inr (Or.inl ⟨Real.pi / 3, Real.pi / 6,
        tileAngles_of_eq D hT.swap (by ring) (by ring) (by ring),
        tgtAngles_of_eq D hG (by ring) (by ring) (by ring)⟩)

/-! ### Table `laczkovich2`: not all angles commensurable -/

/-- **Table `laczkovich2`** (NoSeven paper; Laczkovich 1995 Thm 4.1 with the target shapes of
Thms 2.4, 2.5, for congruent tiles). If the triangle `ABC` is tiled by congruent copies of a tile
some angle of which is not a rational multiple of `π`, then one of the following holds (`α ∉ ℚπ`
throughout):

1. `ABC` is similar to the tile;
2. the tile has angles `(α, β, π/2)` and `ABC` has angles `(α, α, 2β)`;
3. `ABC` is equilateral and the tile has angles `(α, 2π/3 - α, π/3)`;
4. the tile has angles `(α, π - 3α, 2α)` and `ABC` has angles `(α, α, π - 2α)`;
5. the tile has angles `(α, β, 2α + β)` with `3α + 2β = π`, and `ABC` has angles
   `(β, β, 3α)`, `(α + β, α + β, α)`, `(2α, β, α + β)`, `(2α, α, 2β)` or `(α, α, α + 2β)`;
6. the tile has angles `(α, β, 2π/3)` with `β = π/3 - α`, and `ABC` is equilateral or has
   angles `(α, α, α + 3β)`, `(β, β, β + 3α)`, `(α, α + β, α + 2β)`, `(β, α + β, 2α + β)`,
   `(2α, 2β, α + β)`, `(α, 2α, 3β)`, `(β, 2β, 3α)`, `(α, 2β, 2α + β)` or `(β, 2α, α + 2β)`. -/
theorem table_incommensurable (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    SimilarTM D ∨ RightRow D ∨
    (Equilateral D ∧ ∃ α, IrrPi α ∧ TileAngles D α (2 * Real.pi / 3 - α) (Real.pi / 3)) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi - 3 * α) (2 * α) ∧
      TgtAngles D α α (Real.pi - 2 * α)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
        TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
        TgtAngles D α α (α + 2 * β))) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3) ∧
      (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)) := by
  by_cases hs : SimilarTM D
  · exact Or.inl hs
  right
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hs with h | h | h | h | h
  · -- The right-angled tile.
    obtain ⟨α, -, -, -, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi, hj⟩ := h
    left
    obtain ⟨r, hrp, hrq⟩ := fin3_third p q hpq
    have hs3 := angleAt_sum3 D.model hpq hrp.symm hrq.symm
    rcases hγ with rfl | rfl
    · exact rightRow_of D hpq hq hij (hi.trans hp.symm) (hj.trans hp.symm)
    · have hr : D.model.angleAt r = Real.pi / 2 - α := by linarith
      exact rightRow_of D hrq hq hij (hi.trans hr.symm) (hj.trans hr.symm)
  · -- `γ = 2α`.
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, i, j, hij, hi, hj⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨α, hα, ⟨σ, h0, h1, h2⟩, tgt_of_two D hij hi hj⟩))
  · -- An angle `π/3`: `ABC` is equilateral (Lemma P).
    obtain ⟨α, a, b, c, hα, hd⟩ := h
    have heq := Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    exact Or.inr (Or.inl ⟨heq, α, hα, ⟨σ, h0, h1, h2⟩⟩)
  · -- `γ = 2π/3`.
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨α, hα, ⟨σ, h0, h1, h2⟩, hshape⟩)))
  · -- `3α + 2β = π`.
    obtain ⟨α, β, a, b, c, hα, hrel, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨α, β, hα, hrel, ⟨σ, h0, h1, h2⟩, hshape⟩)))

end TriangleTiling.Laczkovich
