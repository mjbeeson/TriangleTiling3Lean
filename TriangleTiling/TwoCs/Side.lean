/-
The side pigeonhole for `lemma:twocs` (as in `lemma:no28` of the isosceles paper, for a general
tile): if exactly one tile on the side `AB` (`target.pts 0`, `target.pts 1`) has its `c` edge there,
then at every vertex strictly inside `AB` another tile on `AB` has its `γ`, at an end of its edge.
-/
import TriangleTiling.TwoCs.Corners
import TriangleTiling.Isosceles.No28

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry

/-- **The side pigeonhole.** If exactly one tile `eT` supported by `AB` has its `c` edge on
`AB`, then at every vertex strictly inside `AB` one of the other supported tiles has its `γ`
angle, at an end of its edge. -/
theorem side_step {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (hγ : Real.pi / 2 < tileγ D)
    (hcorner : ∀ k, D.target.localAngle (D.target.pts k) < tileγ D)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (eT : Fin N × Fin 3)
    (heT : part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) = {eT})
    {V : Plane} (hV : V ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))))
    (hVA : V ≠ D.target.pts 0) (hVB : V ≠ D.target.pts 1) :
    ∃ e ∈ part, e ≠ eT ∧ ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) ∧
      (D.tile e.1).localAngle V = tileγ D := by
  classical
  set A := D.target.pts 0
  set B := D.target.pts 1
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  set Eint := (part.image u ∪ part.image v).filter fun x => x ≠ A ∧ x ≠ B
  have cγA := (corner_counts D hsep hγ 0 (hcorner 0)).1
  have cγB := (corner_counts D hsep hγ 1 (hcorner 1)).1
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy; rw [← hcov]; exact Set.mem_biUnion he hy
  set s := part.erase eT
  -- Each tile of `s` has its `γ` at an end of its edge.
  have hγend : ∀ e ∈ s, (D.tile e.1).localAngle (u e) = tileγ D ∨
      (D.tile e.1).localAngle (v e) = tileγ D := by
    intro e he
    obtain ⟨hne, hep⟩ := Finset.mem_erase.mp he
    refine corner_at_endpoint D hsep e.1 e.2 (Or.inr (Or.inr rfl)) fun h => hne ?_
    have : e ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := Finset.mem_filter.mpr ⟨hep, h⟩
    rw [heT] at this
    exact Finset.mem_singleton.mp this
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = tileγ D then u e else v e
  have hφγ : ∀ e ∈ s, (D.tile e.1).localAngle (φ e) = tileγ D := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hγend e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  have hφE : ∀ e ∈ s, φ e ∈ Eint := by
    intro e he
    have hep := (Finset.mem_erase.mp he).2
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hep)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hep)
    · intro h; have := hφγ e he; rw [h] at this; exact ne_of_angleCount_zero D cγA e.1 this
    · intro h; have := hφγ e he; rw [h] at this; exact ne_of_angleCount_zero D cγB e.1 this
  have hφseg : ∀ e ∈ s, φ e ∈ segment ℝ A B := by
    intro e he
    apply hsub e (Finset.mem_erase.mp he).2
    rcases hφuv e with h | h <;> rw [h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  -- `φ` is injective on `s`.
  have hinj : Set.InjOn φ s := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e (Finset.mem_erase.mp he).2)
        (h1 ▸ hsub e' (Finset.mem_erase.mp he').2)
    · have hfr : φ e ∈ frontier D.target.carrier := tri_side_subset_frontier D.target 0 (hφseg e he)
      have hnc : φ e ∉ Set.range D.target.pts := by
        rintro ⟨j, hj⟩
        have hE := Finset.mem_filter.mp (hφE e he)
        have hc2 := coord_two_of_mem_side D.target (hφseg e he)
        rw [← hj, Tri.coord_vertex] at hc2
        fin_cases j
        · exact hE.2.1 hj.symm
        · exact hE.2.2 hj.symm
        · simp at hc2
      have hle := (side_le D hsep hγ hfr hnc).1
      exact h1 (eq_of_angleCount_le_one D hle (hφγ e he) (heq ▸ hφγ e' he'))
  -- So `φ` maps `s` onto the interior endpoints.
  have hAB : A ≠ B := D.target.indep.injective.ne (by decide)
  have huv : ∀ e ∈ part, u e ≠ v e :=
    fun e _ => (D.tile e.1).indep.injective.ne (fin3_ne_add_one e.2)
  have hchain : Eint.card + 1 ≤ part.card :=
    (segment_chain_endpoints A B hAB part u v huv hcov hdisj).1
  have heTp : eT ∈ part := by
    have : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).1
  have hscard : s.card + 1 = part.card := Finset.card_erase_add_one heTp
  have himg : s.image φ = Eint := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hφE e he
    · rw [Finset.card_image_of_injOn hinj]; omega
  have hVE : V ∈ Eint := Finset.mem_filter.mpr ⟨hV, hVA, hVB⟩
  rw [← himg] at hVE
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hVE
  obtain ⟨hne, hep⟩ := Finset.mem_erase.mp he
  exact ⟨e, hep, hne, (hφuv e).imp Eq.symm Eq.symm, hφγ e he⟩

end TriangleTiling.TwoCs
