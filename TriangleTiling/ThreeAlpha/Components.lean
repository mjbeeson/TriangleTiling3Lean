/-
The connected components of a tiling (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4, section "The connected components of a tiling"): the graph `H`,
`lemma:connectedcomponents`, `lemma:Hcomponents`.

Statements not yet checked by Beeson. Two tiles are connected in `H` if they share two vertices
and do not have the same angles at them. The key fact: two connected tiles are point reflections
of each other through the midpoint of their common edge (their union is a parallelogram). So along
a path in `H` the edge vectors change only by a sign, and the vertices stay in the lattice spanned
by one tile.
-/
import TriangleTiling.TwoCs.Basic
import TriangleTiling.ThreeAlpha.Defs
import TriangleTiling.Tiling.Rays
import TriangleTiling.RightTile.Helper2
import Erdos634.Draft.FluxTurn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry Set

/-- `cross (pts (m+1) - pts m) (P - pts m)` is the coordinate of `P` at `pts (m+2)`, times
`cross (pts (m+1) - pts m) (pts (m+2) - pts m)`. -/
theorem cross_coord (T : Tri) (m : Fin 3) (P : Plane) :
    cross (T.pts (m + 1) - T.pts m) (P - T.pts m) =
      T.basis.coord (m + 2) P * cross (T.pts (m + 1) - T.pts m) (T.pts (m + 2) - T.pts m) := by
  have hP := T.basis.linear_combination_coord_eq_self P
  have hs := Tri.coord_sum T P
  rw [Fin.sum_univ_three] at hP
  simp only [Tri.basis_apply'] at hP
  conv_lhs => rw [← hP]
  fin_cases m <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, cross,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
    generalize T.basis.coord 0 P = c0 at hs ⊢ <;>
    generalize T.basis.coord 1 P = c1 at hs ⊢ <;>
    generalize T.basis.coord 2 P = c2 at hs ⊢
  · linear_combination ((T.pts 1 0 - T.pts 0 0) * T.pts 0 1 - (T.pts 1 1 - T.pts 0 1) * T.pts 0 0) * hs
  · linear_combination ((T.pts 2 0 - T.pts 1 0) * T.pts 1 1 - (T.pts 2 1 - T.pts 1 1) * T.pts 1 0) * hs
  · linear_combination ((T.pts 0 0 - T.pts 2 0) * T.pts 2 1 - (T.pts 0 1 - T.pts 2 1) * T.pts 2 0) * hs

/-- **The point reflection.** Let `U, V, W` be a triangle and `W'` a point on the other side of
`UV` with `∠ V U W' = ∠ U V W` and `∠ U V W' = ∠ V U W`. Then `W' = U + V - W`. -/
theorem reflect_point {U V W W' : Plane} (hUV : U ≠ V)
    (hW : cross (V - U) (W - U) ≠ 0) (hside : cross (V - U) (W' - U) * cross (V - U) (W - U) < 0)
    (hU : ∠ V U W' = ∠ U V W) (hV : ∠ U V W' = ∠ V U W) : W' = U + V - W := by
  set W'' := U + V - W
  have hp : V - U ≠ 0 := sub_ne_zero.mpr hUV.symm
  have hW'U : W' - U ≠ 0 := by
    intro h; rw [h] at hside; simp [cross] at hside
  have hW''U : W'' - U ≠ 0 := by
    intro h
    have : W'' - U = V - W := by simp only [W'']; abel
    rw [this] at h
    have hVW : V = W := sub_eq_zero.mp h
    apply hW; rw [← hVW]; simp [cross]; ring
  -- At `U`.
  have hcrossU : cross (V - U) (W'' - U) = - cross (V - U) (W - U) := by
    simp only [W'', cross, PiLp.sub_apply, PiLp.add_apply]; ring
  have hangU : InnerProductGeometry.angle (V - U) (W' - U) =
      InnerProductGeometry.angle (V - U) (W'' - U) := by
    have e1 : ∠ V U W' = InnerProductGeometry.angle (V - U) (W' - U) := rfl
    have e2 : ∠ U V W = InnerProductGeometry.angle (U - V) (W - V) := rfl
    rw [← e1, hU, e2]
    have : W'' - U = -(W - V) := by simp only [W'']; abel
    rw [this, show U - V = -(V - U) by abel, InnerProductGeometry.angle_neg_left,
      InnerProductGeometry.angle_neg_right]
  obtain ⟨t, ht, htW⟩ := same_ray_of_angle_eq hp hW'U hW''U hangU (by
    rw [hcrossU]; nlinarith [hside])
  -- At `V`.
  have hq : U - V ≠ 0 := sub_ne_zero.mpr hUV
  have hW'V : W' - V ≠ 0 := by
    intro h
    have : W' = V := sub_eq_zero.mp h
    have h0 : cross (V - U) (V - U) = 0 := by simp only [cross]; ring
    rw [this, h0, zero_mul] at hside; exact lt_irrefl 0 hside
  have hW''V : W'' - V ≠ 0 := by
    intro h
    have : W'' - V = U - W := by simp only [W'']; abel
    rw [this] at h
    have hUW : U = W := sub_eq_zero.mp h
    apply hW; simp [← hUW, cross]
  have hangV : InnerProductGeometry.angle (U - V) (W' - V) =
      InnerProductGeometry.angle (U - V) (W'' - V) := by
    have e1 : ∠ U V W' = InnerProductGeometry.angle (U - V) (W' - V) := rfl
    have e2 : ∠ V U W = InnerProductGeometry.angle (V - U) (W - U) := rfl
    rw [← e1, hV, e2]
    have : W'' - V = -(W - U) := by simp only [W'']; abel
    rw [this, show U - V = -(V - U) by abel, InnerProductGeometry.angle_neg_left,
      InnerProductGeometry.angle_neg_right]
    ring
  have hcrossV : ∀ P : Plane, cross (U - V) (P - V) = -cross (V - U) (P - U) := by
    intro P; simp only [cross, PiLp.sub_apply]; ring
  obtain ⟨t', ht', htW'⟩ := same_ray_of_angle_eq hq hW'V hW''V hangV (by
    rw [hcrossV, hcrossV, hcrossU]; nlinarith [hside])
  -- The two rays meet only at `W''`.
  have e : (t - 1) • (V - U) + (t' - t) • (W - U) = 0 := by
    have h1 : W' = U + t • (W'' - U) := by rw [← htW]; abel
    have h2 : W' = V + t' • (W'' - V) := by rw [← htW']; abel
    have : U + t • (W'' - U) = V + t' • (W'' - V) := h1.symm.trans h2
    simp only [W''] at this
    have h3 : (t - 1) • (V - U) + (t' - t) • (W - U) =
        (U + t • (U + V - W - U)) - (V + t' • (U + V - W - V)) := by module
    rw [h3, this, sub_self]
  have c1 := congrArg (cross (V - U)) e
  have hlin : ∀ (x y : ℝ) (p q : Plane), cross (V - U) (x • p + y • q) =
      x * cross (V - U) p + y * cross (V - U) q := by
    intro x y p q; simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hlin] at c1
  have hpp : cross (V - U) (V - U) = 0 := by simp only [cross]; ring
  have h0 : cross (V - U) 0 = 0 := by simp [cross]
  rw [hpp, h0, mul_zero, zero_add] at c1
  have htt : t' = t := by
    rcases mul_eq_zero.mp c1 with h | h
    · linarith
    · exact absurd h hW
  rw [htt, sub_self, zero_smul, add_zero] at e
  have ht1 : t = 1 := by
    rcases smul_eq_zero.mp e with h | h
    · linarith
    · exact absurd h hp
  rw [ht1, one_smul] at htW
  exact (sub_left_inj.mp htW)

/-- The cross product along edge `m` toward the opposite vertex is `det`. -/
theorem cross_edge_det (T : Tri) (m : Fin 3) :
    cross (T.pts (m + 1) - T.pts m) (T.pts (m + 2) - T.pts m) = T.det := by
  fin_cases m <;> simp [cross, Tri.det] <;> ring

/-- The cross product of two edges from a vertex of a triangle is `±det`, so not `0`. -/
theorem cross_vertices_ne (T : Tri) {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    cross (T.pts y - T.pts x) (T.pts z - T.pts x) ≠ 0 := by
  have hd := T.det_ne_zero
  have hanti : ∀ u v : Plane, cross u v = -cross v u := by
    intro u v; simp only [cross]; ring
  have : (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
    revert hxy hxz hyz; revert x y z; decide
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [cross_edge_det]; exact hd
  · rw [hanti, cross_edge_det]; exact neg_ne_zero.mpr hd

section Graph

variable {N : ℕ}

/-- **The graph `H`.** Tiles `i` and `j` are *connected* if they share two vertices (and hence the
edge between them) and do not have the same angles at the vertices of their shared side. -/
def Hconn (D : Dissection N) (i j : Fin N) : Prop :=
  i ≠ j ∧ ∃ k l k' l' : Fin 3, k ≠ l ∧ (D.tile i).pts k = (D.tile j).pts k' ∧
    (D.tile i).pts l = (D.tile j).pts l' ∧
      ¬ ((D.tile i).angleAt k = (D.tile j).angleAt k' ∧ (D.tile i).angleAt l = (D.tile j).angleAt l')

theorem Hconn.symm {D : Dissection N} {i j : Fin N} (h : Hconn D i j) : Hconn D j i := by
  obtain ⟨hij, k, l, k', l', hkl, hU, hV, hn⟩ := h
  have hkl' : k' ≠ l' := by
    intro e; apply hkl; apply (D.tile i).indep.injective; rw [hU, hV, e]
  exact ⟨hij.symm, k', l', k, l, hkl', hU.symm, hV.symm, fun ⟨e1, e2⟩ => hn ⟨e1.symm, e2.symm⟩⟩

/-- The graph `H` on the tiles. -/
def graphH (D : Dissection N) : SimpleGraph (Fin N) where
  Adj i j := Hconn D i j
  symm _ _ h := h.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

end Graph

theorem third_eq : ∀ p q a b : Fin 3, p ≠ q → a ≠ p → a ≠ q → b ≠ p → b ≠ q → a = b := by decide

theorem angleAt_eq_localAngle (T : Tri) (x : Fin 3) : T.angleAt x = T.localAngle (T.pts x) :=
  (Tri.localAngle_vertex T x).symm

section Reflect

variable {N : ℕ} (D : CongruentDissection N)
  (hd : ∀ x y x' y' : Fin 3, x ≠ y → x' ≠ y' →
    dist (D.model.pts x) (D.model.pts y) = dist (D.model.pts x') (D.model.pts y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
include hd

/-- **Connected tiles are point reflections of each other** (their union is a parallelogram):
the vertices of `j` are `O - P` for the vertices `P` of `i`, with the same angles. -/
theorem link_reflect {i j : Fin N} (h : Hconn D.toDissection i j) :
    ∃ O : Plane, (∃ k l : Fin 3, O = (D.tile i).pts k + (D.tile i).pts l) ∧
      ∃ τ : Fin 3 → Fin 3, ∀ x, (D.tile j).pts (τ x) = O - (D.tile i).pts x ∧
        (D.tile j).angleAt (τ x) = (D.tile i).angleAt x := by
  obtain ⟨hij, k, l, k', l', hkl, hU, hV, hn⟩ := h
  set Ti := D.tile i
  set Tj := D.tile j
  have hkl' : k' ≠ l' := by
    intro e; apply hkl; apply Ti.indep.injective; rw [hU, hV, e]
  obtain ⟨w, hwk, hwl⟩ : ∃ w : Fin 3, w ≠ k ∧ w ≠ l :=
    (by decide : ∀ k l : Fin 3, k ≠ l → ∃ w : Fin 3, w ≠ k ∧ w ≠ l) k l hkl
  obtain ⟨w', hw'k, hw'l⟩ : ∃ w : Fin 3, w ≠ k' ∧ w ≠ l' :=
    (by decide : ∀ k l : Fin 3, k ≠ l → ∃ w : Fin 3, w ≠ k ∧ w ≠ l) k' l' hkl'
  obtain ⟨ρi, hρia, hρid⟩ := corner_perm_dist (D.tiles_congruent i)
  obtain ⟨ρj, hρja, hρjd⟩ := corner_perm_dist (D.tiles_congruent j)
  have hai : ∀ x, Ti.angleAt x = D.model.angleAt (ρi x) := fun x => (hρia x).symm
  have haj : ∀ x, Tj.angleAt x = D.model.angleAt (ρj x) := fun x => (hρja x).symm
  have hdist : dist (D.model.pts (ρi k)) (D.model.pts (ρi l)) =
      dist (D.model.pts (ρj k')) (D.model.pts (ρj l')) := by
    rw [← hρid, ← hρjd, hU, hV]
  rcases hd _ _ _ _ (ρi.injective.ne hkl) (ρj.injective.ne hkl') hdist with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact absurd ⟨by rw [hai, haj, e1], by rw [hai, haj, e2]⟩ hn
  have ew : ρi w = ρj w' :=
    third_eq (ρi k) (ρi l) _ _ (ρi.injective.ne hkl) (ρi.injective.ne hwk) (ρi.injective.ne hwl)
      (by rw [e1]; exact ρj.injective.ne hw'l) (by rw [e2]; exact ρj.injective.ne hw'k)
  have ak : Tj.angleAt l' = Ti.angleAt k := by rw [hai, haj, e1]
  have al : Tj.angleAt k' = Ti.angleAt l := by rw [hai, haj, e2]
  have aw : Tj.angleAt w' = Ti.angleAt w := by rw [hai, haj, ew]
  set U := Ti.pts k
  set V := Ti.pts l
  set W := Ti.pts w
  set W' := Tj.pts w'
  have hUV : U ≠ V := fun e => hkl (Ti.indep.injective e)
  -- The angles at `U` and `V`.
  have hU' : ∠ V U W' = ∠ U V W := by
    have h1 := TwoCs.corner_angle_eq Tj (j := k') hkl'.symm hw'k (Ne.symm hw'l)
    have h2 := TwoCs.corner_angle_eq Ti (j := l) hkl hwl (Ne.symm hwk)
    rw [← angleAt_eq_localAngle, al, ← hU, ← hV] at h1
    rw [← angleAt_eq_localAngle] at h2
    exact h1.symm.trans h2
  have hV' : ∠ U V W' = ∠ V U W := by
    have h1 := TwoCs.corner_angle_eq Tj (j := l') hkl' hw'l (Ne.symm hw'k)
    have h2 := TwoCs.corner_angle_eq Ti (j := k) hkl.symm hwk (Ne.symm hwl)
    rw [← angleAt_eq_localAngle, ak, ← hU, ← hV] at h1
    rw [← angleAt_eq_localAngle] at h2
    exact h1.symm.trans h2
  -- `W'` is on the other side of `UV`.
  obtain ⟨m, hm⟩ : ∃ m : Fin 3, (m = k ∧ m + 1 = l) ∨ (m = l ∧ m + 1 = k) :=
    (by decide : ∀ q r : Fin 3, q ≠ r → ∃ m : Fin 3, (m = q ∧ m + 1 = r) ∨ (m = r ∧ m + 1 = q))
      k l hkl
  have hm2 : m + 2 = w := by
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact third_eq m (m + 1) _ _ (by fin_cases m <;> decide) (by fin_cases m <;> decide)
        (by fin_cases m <;> decide) hwk hwl
    · exact third_eq (m + 1) m _ _ (by fin_cases m <;> decide) (by fin_cases m <;> decide)
        (by fin_cases m <;> decide) hwk hwl
  have hseg : ∀ P : Plane, openSegment ℝ (Ti.pts m) (Ti.pts (m + 1)) = openSegment ℝ U V ∨
      True := fun _ => Or.inr trivial
  have hQ : AffineMap.lineMap U V (1 / 2 : ℝ) ∈ openSegment ℝ (Ti.pts m) (Ti.pts (m + 1)) := by
    have : AffineMap.lineMap U V (1 / 2 : ℝ) ∈ openSegment ℝ U V := by
      rw [openSegment_eq_image_lineMap]; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · rw [openSegment_symm]; exact this
  have hTjc : ∀ x, Tj.pts x ∈ Tj.carrier := fun x => subset_convexHull ℝ _ ⟨x, rfl⟩
  have hQj : AffineMap.lineMap U V (1 / 2 : ℝ) ∈ Tj.carrier := by
    apply Tj.convex.segment_subset (hU ▸ hTjc k') (hV ▸ hTjc l')
    rw [segment_eq_image_lineMap]; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hside0 := tile_side_of_openSegment D.toDissection hQ (Ne.symm hij) hQj W' (hTjc w')
  rw [hm2] at hside0
  have hanti : ∀ P : Plane, cross (U - V) (P - V) = -cross (V - U) (P - U) := by
    intro P; simp only [cross, PiLp.sub_apply]; ring
  have hcW' : cross (V - U) (W' - U) ≠ 0 := by
    have := cross_vertices_ne Tj hkl' hw'k.symm hw'l.symm
    rwa [← hU, ← hV] at this
  have hcW : cross (V - U) (W - U) ≠ 0 := cross_vertices_ne Ti hkl hwk.symm hwl.symm
  have hcoord := cross_coord Ti m W'
  have hcoordW := cross_coord Ti m W
  rw [hm2] at hcoord hcoordW
  have hW1 : Ti.basis.coord w W = 1 := by simp only [W]; rw [Tri.coord_vertex, if_pos rfl]
  rw [hW1, one_mul] at hcoordW
  have hdet : cross (Ti.pts (m + 1) - Ti.pts m) (Ti.pts w - Ti.pts m) ≠ 0 := by
    rw [← hm2, cross_edge_det]; exact Ti.det_ne_zero
  have hneg : Ti.basis.coord w W' < 0 := by
    rcases lt_or_eq_of_le hside0 with h | h
    · exact h
    · exfalso
      rw [h, zero_mul] at hcoord
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcW' hcoord
      · rw [hanti] at hcoord; exact hcW' (neg_eq_zero.mp hcoord)
  have hside : cross (V - U) (W' - U) * cross (V - U) (W - U) < 0 := by
    have key : cross (Ti.pts (m + 1) - Ti.pts m) (W' - Ti.pts m) *
        cross (Ti.pts (m + 1) - Ti.pts m) (W - Ti.pts m) < 0 := by
      rw [hcoord, hcoordW]
      have : 0 < (cross (Ti.pts (m + 1) - Ti.pts m) (Ti.pts w - Ti.pts m)) ^ 2 := by positivity
      nlinarith
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key
    · rw [hanti, hanti] at key; linarith
  have hW' : W' = U + V - W := reflect_point hUV hcW hside hU' hV'
  refine ⟨U + V, ⟨k, l, rfl⟩, fun x => if x = k then l' else if x = l then k' else w',
    fun x => ?_⟩
  dsimp only
  by_cases hxk : x = k
  · rw [if_pos hxk, hxk]
    exact ⟨by rw [← hV]; abel, ak⟩
  · by_cases hxl : x = l
    · rw [if_neg hxk, if_pos hxl, hxl]
      exact ⟨by rw [← hU]; abel, al⟩
    · simp only [if_neg hxk, if_neg hxl]
      have hxw : x = w := third_eq k l x w hkl hxk hxl hwk hwl
      subst hxw
      exact ⟨hW'.trans (by abel), aw⟩

/-- **Along a path in `H`**, tile `j` is tile `i` translated and possibly reflected through a
point: its vertices are `O ± P` for the vertices `P` of `i`, with the same angles. -/
theorem reach_reflect {i j : Fin N} (h : (graphH D.toDissection).Reachable i j) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ O : Plane, ∃ σ : Fin 3 → Fin 3, ∀ x,
      (D.tile j).pts (σ x) = O + s • (D.tile i).pts x ∧
        (D.tile j).angleAt (σ x) = (D.tile i).angleAt x := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨1, Or.inl rfl, 0, id, fun x => ⟨by simp, rfl⟩⟩
  | cons hadj p ih =>
    obtain ⟨O, -, τ, hτ⟩ := link_reflect D hd hadj
    obtain ⟨s, hs, O', σ, hσ⟩ := ih
    refine ⟨-s, by rcases hs with rfl | rfl <;> simp, O' + s • O, σ ∘ τ, fun x => ?_⟩
    obtain ⟨h1, h2⟩ := hτ x
    obtain ⟨h3, h4⟩ := hσ (τ x)
    refine ⟨?_, by simp only [Function.comp, h4, h2]⟩
    simp only [Function.comp, h3, h1, smul_sub, neg_smul]
    abel

/-- **The lattice of a component.** Every vertex of a tile reachable from `i₀` is an integer
combination `pts₀ + p u + q v` of the vertices of tile `i₀` (`u, v` its edges at vertex `0`). -/
theorem reach_lattice {i₀ i : Fin N} (h : (graphH D.toDissection).Reachable i₀ i) :
    ∀ x, ∃ p q : ℤ, (D.tile i).pts x = (D.tile i₀).pts 0 +
      (p : ℝ) • ((D.tile i₀).pts 1 - (D.tile i₀).pts 0) +
        (q : ℝ) • ((D.tile i₀).pts 2 - (D.tile i₀).pts 0) := by
  set O := (D.tile i₀).pts 0
  set u := (D.tile i₀).pts 1 - (D.tile i₀).pts 0
  set v := (D.tile i₀).pts 2 - (D.tile i₀).pts 0
  let L : Plane → Prop := fun P => ∃ p q : ℤ, P = O + (p : ℝ) • u + (q : ℝ) • v
  have hL0 : ∀ x, L ((D.tile i₀).pts x) := by
    intro x
    fin_cases x
    · exact ⟨0, 0, by simp [O]⟩
    · exact ⟨1, 0, by simp [O, u]⟩
    · exact ⟨0, 1, by simp [O, v]⟩
  have hstep : ∀ {a b : Fin N}, (graphH D.toDissection).Walk a b → (∀ x, L ((D.tile a).pts x)) →
      ∀ x, L ((D.tile b).pts x) := by
    intro a b w
    induction w with
    | nil => exact id
    | cons hadj w ih =>
      intro ha
      apply ih
      obtain ⟨O', ⟨k, l, hO'⟩, τ, hτ⟩ := link_reflect D hd hadj
      -- `τ` is a bijection, so every vertex of the next tile is `O' - P`.
      have hinj : Function.Injective τ := by
        intro x y hxy
        have := (hτ x).1
        rw [hxy, (hτ y).1] at this
        exact ((D.tile _).indep.injective (sub_right_injective this)).symm
      have hsurj := Finite.surjective_of_injective hinj
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      rw [(hτ x).1, hO']
      obtain ⟨p1, q1, e1⟩ := ha k
      obtain ⟨p2, q2, e2⟩ := ha l
      obtain ⟨p3, q3, e3⟩ := ha x
      refine ⟨p1 + p2 - p3, q1 + q2 - q3, ?_⟩
      rw [e1, e2, e3]
      push_cast
      module
  obtain ⟨w⟩ := h
  exact hstep w hL0


end Reflect


theorem fin3_pair : ∀ x y x' y' z : Fin 3, x ≠ y → x' ≠ y' → z ≠ x → z ≠ y → z ≠ x' → z ≠ y' →
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by decide

theorem fin3_share : ∀ p q r s : Fin 3, p ≠ q → r ≠ s → ¬((p = r ∧ q = s) ∨ (p = s ∧ q = r)) →
    (p = r ∧ q ≠ s) ∨ (p = s ∧ q ≠ r) ∨ (q = r ∧ p ≠ s) ∨ (q = s ∧ p ≠ r) := by decide

/-- Two different edges of a triangle are not parallel. -/
theorem edges_cross_ne (T : Tri) {p q r s : Fin 3} (hpq : p ≠ q) (hrs : r ≠ s)
    (hne : ¬((p = r ∧ q = s) ∨ (p = s ∧ q = r))) :
    cross (T.pts q - T.pts p) (T.pts s - T.pts r) ≠ 0 := by
  have hsplit : ∀ P Q R : Plane, cross (Q - P) (R - Q) = cross (Q - P) (R - P) := by
    intro P Q R; simp only [cross, PiLp.sub_apply]; ring
  have hsplit' : ∀ P Q R : Plane, cross (Q - P) (Q - R) = -cross (Q - P) (R - P) := by
    intro P Q R; simp only [cross, PiLp.sub_apply]; ring
  have hflip : ∀ P Q R : Plane, cross (Q - P) (P - R) = -cross (Q - P) (R - P) := by
    intro P Q R; simp only [cross, PiLp.sub_apply]; ring
  rcases fin3_share p q r s hpq hrs hne with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact cross_vertices_ne T hpq hrs h
  · rw [hflip, neg_ne_zero]; exact cross_vertices_ne T hpq (Ne.symm hrs) h
  · rw [hsplit]; exact cross_vertices_ne T hpq h hrs
  · rw [hsplit', neg_ne_zero]; exact cross_vertices_ne T hpq h (Ne.symm hrs)

/-- The distance between two vertices is the side opposite the third. -/
theorem pair_dist (T : Tri) {x y : Fin 3} (hxy : x ≠ y) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ dist (T.pts x) (T.pts y) = T.oppLen z := by
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Fin 3, z ≠ x ∧ z ≠ y :=
    (by decide : ∀ k l : Fin 3, k ≠ l → ∃ w : Fin 3, w ≠ k ∧ w ≠ l) x y hxy
  refine ⟨z, hzx, hzy, ?_⟩
  unfold Tri.oppLen
  have : (x = z + 1 ∧ y = z + 2) ∨ (x = z + 2 ∧ y = z + 1) := by
    revert hxy hzx hzy; revert x y z; decide
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact dist_comm _ _

/-- With the sides of the tile distinct, a pair of model vertices is determined by its distance. -/
theorem model_pairs {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∀ x y x' y' : Fin 3, x ≠ y → x' ≠ y' →
      dist (D.model.pts x) (D.model.pts y) = dist (D.model.pts x') (D.model.pts y') →
        (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain ⟨σ, -, -, -, l0, l1, l2⟩ := hT
  have hinj : ∀ z z' : Fin 3, D.model.oppLen z = D.model.oppLen z' → z = z' := by
    intro z z' h
    obtain ⟨p, rfl⟩ := σ.surjective z
    obtain ⟨q, rfl⟩ := σ.surjective z'
    congr 1
    have hv : ∀ r : Fin 3, D.model.oppLen (σ r) = ![a, b, c] r := by
      intro r; fin_cases r
      · exact l0
      · exact l1
      · exact l2
    rw [hv p, hv q] at h
    fin_cases p <;> fin_cases q <;> simp only [Matrix.cons_val] at h <;> first
      | rfl | exact absurd h hab | exact absurd h.symm hab | exact absurd h hbc
      | exact absurd h.symm hbc | exact absurd h hac | exact absurd h.symm hac
  intro x y x' y' hxy hx'y' h
  obtain ⟨z, hzx, hzy, hz⟩ := pair_dist D.model hxy
  obtain ⟨z', hzx', hzy', hz'⟩ := pair_dist D.model hx'y'
  have hzz := hinj z z' (hz.symm.trans (h.trans hz'))
  subst hzz
  exact fin3_pair x y x' y' z hxy hx'y' hzx hzy hzx' hzy'

/-- **Lemma `lemma:connectedcomponents`.** Assume the tile is not isosceles. In any connected set
of a tiling, any two edges of the same length are parallel or on the same line. Two tile edges of
different lengths lying on the same line do not belong to the same connected component.

"Not isosceles" is read as `a, b, c` distinct; a connected set is read through `H`-paths (tiles
joined by a path in `H`). -/
theorem connectedcomponents {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (∀ i j : Fin N, (graphH D.toDissection).Reachable i j → ∀ m m' : Fin 3,
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) =
          dist ((D.tile j).pts m') ((D.tile j).pts (m' + 1)) →
        ∃ r : ℝ, r ≠ 0 ∧ (D.tile j).pts (m' + 1) - (D.tile j).pts m' =
          r • ((D.tile i).pts (m + 1) - (D.tile i).pts m)) ∧
      (∀ (i j : Fin N) (m m' : Fin 3),
        Collinear ℝ {(D.tile i).pts m, (D.tile i).pts (m + 1), (D.tile j).pts m',
          (D.tile j).pts (m' + 1)} →
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠
          dist ((D.tile j).pts m') ((D.tile j).pts (m' + 1)) →
        ¬ (graphH D.toDissection).Reachable i j) := by
  have hd := model_pairs D hT hab hbc hac
  -- Pairs of vertices of a tile are determined by their distance.
  have htile : ∀ (i : Fin N) (x y x' y' : Fin 3), x ≠ y → x' ≠ y' →
      dist ((D.tile i).pts x) ((D.tile i).pts y) = dist ((D.tile i).pts x') ((D.tile i).pts y') →
        (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
    intro i x y x' y' hxy hx'y' h
    obtain ⟨ρ, -, hρd⟩ := corner_perm_dist (D.tiles_congruent i)
    rw [hρd, hρd] at h
    rcases hd _ _ _ _ (ρ.injective.ne hxy) (ρ.injective.ne hx'y') h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨ρ.injective e1, ρ.injective e2⟩
    · exact Or.inr ⟨ρ.injective e1, ρ.injective e2⟩
  -- The edge of `j` corresponding to an edge of `i`.
  have hcorr : ∀ i j : Fin N, (graphH D.toDissection).Reachable i j → ∀ m' : Fin 3,
      ∃ (s : ℝ) (y y' : Fin 3), (s = 1 ∨ s = -1) ∧ y ≠ y' ∧
        (D.tile j).pts (m' + 1) - (D.tile j).pts m' = s • ((D.tile i).pts y' - (D.tile i).pts y) ∧
        dist ((D.tile j).pts m') ((D.tile j).pts (m' + 1)) =
          dist ((D.tile i).pts y) ((D.tile i).pts y') := by
    intro i j h m'
    obtain ⟨s, hs, O, σ, hσ⟩ := reach_reflect D hd h
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have hinj : Function.Injective σ := by
      intro x y hxy
      have := (hσ x).1
      rw [hxy, (hσ y).1] at this
      have := smul_right_injective Plane hs0 (add_left_cancel this)
      exact ((D.tile i).indep.injective this).symm
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj m'
    obtain ⟨y', hy'⟩ := Finite.surjective_of_injective hinj (m' + 1)
    have hyy : y ≠ y' := by
      rintro rfl; rw [hy] at hy'; exact fin3_ne_add_one m' hy'
    refine ⟨s, y, y', hs, hyy, ?_, ?_⟩
    · rw [← hy', ← hy, (hσ y).1, (hσ y').1, smul_sub]; abel
    · rw [← hy', ← hy, (hσ y).1, (hσ y').1, dist_add_left, dist_smul₀]
      rcases hs with rfl | rfl <;> simp
  refine ⟨fun i j h m m' hlen => ?_, fun i j m m' hcol hne h => ?_⟩
  · obtain ⟨s, y, y', hs, hyy, hv, hd'⟩ := hcorr i j h m'
    rcases htile i y y' m (m + 1) hyy (fin3_ne_add_one m) (hd'.symm.trans hlen.symm) with
      ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨s, by rcases hs with rfl | rfl <;> norm_num, ?_⟩
      rw [hv, e1, e2]
    · refine ⟨-s, by rcases hs with rfl | rfl <;> norm_num, ?_⟩
      rw [hv, e1, e2, neg_smul, ← smul_neg, neg_sub]
  · obtain ⟨s, y, y', hs, hyy, hv, hd'⟩ := hcorr i j h m'
    -- `{y, y'}` is another edge of `i`, parallel to edge `m`: impossible.
    have hpair : ¬ ((m = y ∧ m + 1 = y') ∨ (m = y' ∧ m + 1 = y)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne hd'.symm
      · exact hne ((dist_comm _ _).trans hd'.symm)
    have hcross : cross ((D.tile i).pts (m + 1) - (D.tile i).pts m)
        ((D.tile i).pts y' - (D.tile i).pts y) = 0 := by
      rw [collinear_iff_of_mem (p₀ := (D.tile i).pts m) (by simp)] at hcol
      obtain ⟨d, hd⟩ := hcol
      have hp : ∀ P ∈ ({(D.tile i).pts m, (D.tile i).pts (m + 1), (D.tile j).pts m',
          (D.tile j).pts (m' + 1)} : Set Plane), ∃ r : ℝ, P = r • d +ᵥ (D.tile i).pts m := hd
      obtain ⟨r1, e1⟩ := hp ((D.tile i).pts (m + 1)) (by simp)
      obtain ⟨r2, e2⟩ := hp ((D.tile j).pts m') (by simp)
      obtain ⟨r3, e3⟩ := hp ((D.tile j).pts (m' + 1)) (by simp)
      have hv' : (D.tile i).pts y' - (D.tile i).pts y = s • ((r3 - r2) • d) := by
        have : (D.tile j).pts (m' + 1) - (D.tile j).pts m' = (r3 - r2) • d := by
          rw [e2, e3, vadd_eq_add, vadd_eq_add, sub_smul]; abel
        rw [hv] at this
        rcases hs with rfl | rfl
        · rw [one_smul] at this; rw [this, one_smul]
        · rw [neg_one_smul, neg_sub] at this
          rw [neg_one_smul, ← this, neg_sub]
      rw [e1, vadd_eq_add, add_sub_cancel_right, hv']
      simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
    exact edges_cross_ne (D.tile i) (fin3_ne_add_one m) hyy hpair hcross

/-- **Lemma `lemma:Hcomponents`.** Suppose there is an `N`-tiling of `ABC` by the tile with angles
`α, β, γ`, and the tile is not isosceles. Let `E` be a connected component of the tiling (the
tiles joined to `i₀` by paths in `H`). Then the tiling restricted to `E` is a lattice tiling: its
vertices lie on the lattice points of a lattice.

The printed hypothesis is `α ≠ β`; the Lean proof uses `a, b, c` distinct (it holds whenever
`3α + 2β = π` and `α ∉ ℚπ`). -/
theorem Hcomponents {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (i₀ : Fin N) :
    ∃ O u v : Plane, cross u v ≠ 0 ∧
      ∀ i, (graphH D.toDissection).Reachable i₀ i → ∀ x, ∃ p q : ℤ,
        (D.tile i).pts x = O + (p : ℝ) • u + (q : ℝ) • v := by
  refine ⟨(D.tile i₀).pts 0, (D.tile i₀).pts 1 - (D.tile i₀).pts 0,
    (D.tile i₀).pts 2 - (D.tile i₀).pts 0, ?_, fun i h => reach_lattice D (model_pairs D hT hab hbc hac) h⟩
  have := cross_edge_det (D.tile i₀) 0
  simp only [Fin.isValue, zero_add] at this
  rw [this]; exact (D.tile i₀).det_ne_zero

end TriangleTiling.ThreeAlpha
