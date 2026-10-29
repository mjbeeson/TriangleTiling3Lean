/-
Scaling a tiling (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4):
`lemma:scaling`.

Statement not yet checked by Beeson. Multiplying every point by `κ > 0` carries an `N`-tiling of
`ABC` by the tile `(a, b, c)` to an `N`-tiling of `κ ABC` by the tile `(κa, κb, κc)`. Adjacency of
tiles is unchanged, so the proper colourings, and hence `M` (the sum of a colouring), are the same.
-/
import TriangleTiling.Laczkovich.ThreeAlpha
import TriangleTiling.ThreeAlpha.ARelation

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry Set
open scoped Pointwise

/-- The triangle `T` scaled by `κ ≠ 0` about the origin. -/
noncomputable def scaleTri (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) : Tri where
  pts := fun k => κ • T.pts k
  indep := by
    have := T.indep.map' (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).toLinearMap.toAffineMap
      (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).injective
    convert this using 1

theorem scale_carrier (T : Tri) {κ : ℝ} (hκ : κ ≠ 0) :
    (scaleTri T κ hκ).carrier = κ • T.carrier := by
  unfold Tri.carrier scaleTri
  rw [← convexHull_smul, Set.smul_set_range]

theorem scale_edge (T : Tri) {κ : ℝ} (hκ : κ ≠ 0) (k : Fin 3) :
    (scaleTri T κ hκ).edge k = (κ • ·) '' T.edge k := by
  unfold Tri.edge scaleTri
  exact (image_segment ℝ (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).toLinearMap.toAffineMap
    (T.pts k) (T.pts (k + 1))).symm

theorem scale_congruent {T U : Tri} (h : T.Congruent U) {κ : ℝ} (hκ : 0 < κ) :
    (scaleTri T κ hκ.ne').Congruent (scaleTri U κ hκ.ne') := by
  obtain ⟨f, σ, hf⟩ := h
  have h0 := hκ.ne'
  let e : Plane ≃ Plane :=
    { toFun := fun x => κ • f (κ⁻¹ • x)
      invFun := fun x => κ • f.symm (κ⁻¹ • x)
      left_inv := fun x => by simp [h0]
      right_inv := fun x => by simp [h0] }
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    show dist (κ • f (κ⁻¹ • x)) (κ • f (κ⁻¹ • y)) = dist x y
    rw [dist_smul₀, f.dist_eq, dist_smul₀, ← mul_assoc, norm_inv, mul_inv_cancel₀ (by simpa using h0),
      one_mul]
  refine ⟨⟨e, hiso⟩, σ, fun k => ?_⟩
  show κ • f (κ⁻¹ • (κ • T.pts k)) = κ • U.pts (σ k)
  rw [inv_smul_smul₀ h0, hf]

theorem scale_angleAt (T : Tri) {κ : ℝ} (hκ : κ ≠ 0) (k : Fin 3) :
    (scaleTri T κ hκ).angleAt k = T.angleAt k := by
  unfold Tri.angleAt cornerAngle scaleTri EuclideanGeometry.angle
  simp only [vsub_eq_sub, ← smul_sub]
  exact InnerProductGeometry.angle_smul_smul hκ _ _

theorem scale_oppLen (T : Tri) {κ : ℝ} (hκ : 0 < κ) (k : Fin 3) :
    (scaleTri T κ hκ.ne').oppLen k = κ * T.oppLen k := by
  unfold Tri.oppLen scaleTri
  simp only
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hκ]

variable {N : ℕ}

/-- The dissection `D` scaled by `κ > 0`. -/
noncomputable def scaleDissection (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) :
    CongruentDissection N where
  target := scaleTri D.target κ hκ.ne'
  tile i := scaleTri (D.tile i) κ hκ.ne'
  covers := by
    simp only [scale_carrier]
    rw [← Set.smul_set_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    simp only [scale_carrier, interior_smul₀ hκ.ne']
    rw [← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective Plane hκ.ne')).mpr (D.interiors_disjoint hij)
  model := scaleTri D.model κ hκ.ne'
  tiles_congruent i := scale_congruent (D.tiles_congruent i) hκ

theorem scale_adj (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) (i j : Fin N) :
    (scaleDissection D hκ).toDissection.Adj i j ↔ D.toDissection.Adj i j := by
  have h0 := hκ.ne'
  simp only [Dissection.Adj, scaleDissection, scale_edge]
  constructor
  · rintro ⟨hne, k, l, p, q, hpq, ⟨p1, hp1, rfl⟩, ⟨q1, hq1, rfl⟩, ⟨p2, hp2, e1⟩, ⟨q2, hq2, e2⟩⟩
    have e1 := smul_right_injective Plane h0 e1
    have e2 := smul_right_injective Plane h0 e2
    subst e1 e2
    exact ⟨hne, k, l, p2, q2, fun h => hpq (by rw [h]), hp1, hq1, hp2, hq2⟩
  · rintro ⟨hne, k, l, p, q, hpq, h1, h2, h3, h4⟩
    exact ⟨hne, k, l, κ • p, κ • q, fun h => hpq (smul_right_injective Plane h0 h),
      ⟨p, h1, rfl⟩, ⟨q, h2, rfl⟩, ⟨p, h3, rfl⟩, ⟨q, h4, rfl⟩⟩

/-- **Lemma `lemma:scaling`.** If triangle `ABC` is `N`-tiled, and we multiply each side of the tile
`(a, b, c)` by a positive number `κ`, and rescale triangle `ABC` by the same factor `κ`, then we
still have a tiling, with the same `N`, `M`, and `s = a/c`. If `s` is rational, after a suitable
scaling we can assume the tile has integer sides.

`M` is the sum of a proper colouring; the scaled tiling has exactly the same proper colourings. The
second part assumes `3α + 2β = π`, as throughout the paper. -/
theorem scaling (D : CongruentDissection N) {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) :
    (∀ κ : ℝ, 0 < κ → ∃ D' : CongruentDissection N,
      (∀ k, D'.target.pts k = κ • D.target.pts k) ∧
      TileSides D' α β γ (κ * a) (κ * b) (κ * c) ∧
      (∀ ε : Fin N → ℤ, D'.toDissection.ProperColouring ε ↔ D.toDissection.ProperColouring ε) ∧
      (κ * a) / (κ * c) = a / c) ∧
    (3 * α + 2 * β = Real.pi → (∃ q : ℚ, a / c = q) →
      ∃ κ : ℝ, 0 < κ ∧ ∃ x y z : ℤ, κ * a = x ∧ κ * b = y ∧ κ * c = z) := by
  refine ⟨fun κ hκ => ⟨scaleDissection D hκ, fun k => by rfl, ?_, fun ε => ?_, ?_⟩, fun hrel hq => ?_⟩
  · obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [scaleDissection, scale_angleAt, scale_oppLen _ hκ, *]
  · simp only [Dissection.ProperColouring, scale_adj D hκ]
  · rw [mul_div_mul_left _ _ hκ.ne']
  · -- `b = c - a²/c` (`lemma:anglesOK`), read off the relabelled model.
    obtain ⟨τ, hα, hβ, -, la, lb, lc⟩ := relabel_facts D (threeAlphaData_of_sides D hrel hT)
    set T := (relabelModel D τ).model
    have hABC : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
      convert T.indep using 1; ext k : 1; fin_cases k <;> rfl
    have hb := (anglesOK hABC).mp (by
      rw [angle_comm (T.pts 0)]
      simp only [tileα, tileβ] at hα hβ
      rw [hα, hβ, hrel])
    rw [lb, lc, la] at hb
    have hc : 0 < c := lc ▸ dist_pos.mpr (T.indep.injective.ne (by decide))
    obtain ⟨q, hq⟩ := hq
    have ha : a = q * c := by rw [← hq]; field_simp
    refine ⟨(q.den : ℝ) ^ 2 / c, by positivity, q.num * q.den, q.den ^ 2 - q.num ^ 2, q.den ^ 2, ?_, ?_, ?_⟩
    · have hqd : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
      rw [ha]; push_cast; field_simp; rw [← hqd]; ring
    · have hqd : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
      rw [hb, ha]; push_cast; field_simp; rw [← hqd]; ring
    · push_cast; field_simp

end TriangleTiling.ThreeAlpha
