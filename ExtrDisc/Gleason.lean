import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Homeomorph

variable {A B C D : Type _} {E : Set D} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace C] [TopologicalSpace D]
  {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
  {π : D → A} (π_cont : Continuous π) (π_surj : π.Surjective)
  (image_ne_top : ∀ E₀ : Set E, E₀ ≠ ⊤ → IsClosed E₀ → ρ '' E₀ ≠ ⊤)

open Function Set

/-- Lemma 2.1 -/
lemma image_subset_closure_compl_image_compl {G : Set E} (hG : IsOpen G) :
    ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  by_cases G_empty : G = ∅
  · simpa only [G_empty, image_empty] using empty_subset _
  · intro a ha
    rw [mem_closure_iff]
    intro N hN ha'
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    have non_empty : (G ∩ ρ⁻¹' N).Nonempty := ⟨e, mem_inter he <| mem_preimage.mpr ha'⟩
    have is_open : IsOpen <| G ∩ ρ⁻¹' N := hG.inter <| hN.preimage ρ_cont
    have ne_top : ρ '' (G ∩ ρ⁻¹' N)ᶜ ≠ ⊤ := image_ne_top _ (compl_ne_univ.mpr non_empty)
                                              is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_top with ⟨x, hx⟩
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := (compl_subset_compl.mpr <| image_subset ρ <|
                                    compl_subset_compl.mpr <| G.inter_subset_left _) hx
    rcases ρ_surj x with ⟨y, rfl⟩
    have hy : y ∈ G ∩ ρ⁻¹' N := not_mem_compl_iff.mp <| (not_imp_not.mpr <| mem_image_of_mem ρ) <|
                                  (mem_compl_iff _ _).mp hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

/-- Lemma 2.2 -/
lemma disjoint_of_extremally_disconnected [ExtremallyDisconnected A] {U₁ U₂ : Set A}
    (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) : Disjoint (closure U₁) (closure U₂) :=
  Disjoint.closure_left (h.closure_right hU₁) <| ExtremallyDisconnected.open_closure U₂ hU₂

lemma compact_to_T2_injective [T2Space A] [ExtremallyDisconnected A] [T2Space E] [CompactSpace E] :
    ρ.Injective := by
  intro x y h_eq_im
  by_contra h
  rcases t2_separation h with ⟨G₁, G₂, hG₁, hG₂, hxG₁, hyG₂, hG⟩
  have open1 : IsOpen ((ρ '' (G₁ᶜ))ᶜ)
  · simp only [isOpen_compl_iff]
    apply IsCompact.isClosed
    refine' IsCompact.image (IsClosed.isCompact _) ρ_cont
    simpa only [isClosed_compl_iff]
  have open2 : IsOpen ((ρ '' (G₂ᶜ))ᶜ)
  · simp only [isOpen_compl_iff]
    apply IsCompact.isClosed
    refine' IsCompact.image (IsClosed.isCompact _) ρ_cont
    simpa only [isClosed_compl_iff]
  have disj : Disjoint ((ρ '' (G₁ᶜ))ᶜ) ((ρ '' (G₂ᶜ))ᶜ)
  · rw [disjoint_compl_left_iff_subset]
    refine' subset_trans (subset_image_compl ρ_surj) _
    simp only [compl_compl, image_subset_iff]
    refine' subset_trans _ (subset_preimage_image _ _)
    rw [← disjoint_compl_left_iff_subset]
    simpa only [compl_compl]
  replace disj := disjoint_of_extremally_disconnected disj open1 open2
  have oups₁ := image_subset_closure_compl_image_compl ρ_cont ρ_surj image_ne_top hG₁
  have oups₂ := image_subset_closure_compl_image_compl ρ_cont ρ_surj image_ne_top hG₂
  have mem₁ : ρ x ∈ ρ '' G₁
  · exact mem_image_of_mem _ hxG₁
  have mem₂ : ρ x ∈ ρ '' G₂
  · rw [h_eq_im]
    exact mem_image_of_mem _ hyG₂
  have mem : ρ x ∈ (closure ((ρ '' G₁ᶜ)ᶜ)) ∩ (closure ((ρ '' G₂ᶜ)ᶜ)) := ⟨oups₁ mem₁, oups₂ mem₂⟩
  exact (disj.ne_of_mem mem.1 mem.2) rfl

/-- Lemma 2.3 -/
noncomputable def compact_to_T2_homeomorph [T2Space A] [ExtremallyDisconnected A] [T2Space E]
    [CompactSpace E] : E ≃ₜ A :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨compact_to_T2_injective ρ_cont ρ_surj image_ne_top, ρ_surj⟩) ρ_cont

lemma h1 {E₀ : Set E} (h : E₀ ≠ ⊤) : (E₀ : Set D) ⊂ E := by
  sorry

lemma h2 {E₀ : Set E} (h : IsClosed E₀) : IsClosed (E₀ : Set D) := by
  sorry

lemma h3 {E₀ : Set E} (h : restrict E π '' E₀ = ⊤) : π '' E₀ = ⊤ := by
  sorry

/-- Lemma 2.4 -/
lemma exists_image_ne_top [T2Space A] [CompactSpace A] [T2Space D] [CompactSpace D] :
    ∃ E : Set D, CompactSpace E ∧ π '' E = ⊤ ∧
    ∀ E₀ : Set E, E₀ ≠ ⊤ → IsClosed E₀ → E.restrict π '' E₀ ≠ ⊤ := by
  -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set D | IsClosed E ∧ π '' E = univ}
  -- Checking the Chain condition
  have chain_cond : (∀ (c : Set (Set ↑(D))),
      c ⊆ S →
      IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D)), s ∈ c → lb ⊆ s) := by
    intro Ch h hCh
    let M := sInter Ch
    use M
    constructor
    · constructor
      · apply isClosed_sInter
        intro N hN
        exact (h hN).1
      --Next, we need to show that the image of M is all of A
      · by_cases h₂ : Nonempty Ch
        rotate_left 1
        -- Case that `Ch` is empty
        · simp at h₂
          rw [←eq_empty_iff_forall_not_mem] at h₂
          revert M
          rw [h₂, sInter_empty]
          simp
          exact range_iff_surjective.mpr π_surj
        -- Now we assume that `Ch` is nonempty
        · ext x
          refine' ⟨ fun _ => trivial , fun _ => _ ⟩
          rw [mem_image]
          change Set.Nonempty {x_1 : D | x_1 ∈ M ∧ π x_1 = x}
          let Z : Ch → Set (D) := fun X => X ∩ π⁻¹' {x}
          suffices Set.Nonempty <| ⋂ (X : Ch), (X: Set (D)) ∩ π⁻¹' {x} by
            convert this
            rw [← iInter_inter, ←  sInter_eq_iInter]
            rw [←setOf_inter_eq_sep, inter_comm]
            congr
          -- Using this result `nonempty_iInter_of_...` introduces a lot of unnecessary checks
          have assumps : ∀ (i : ↑Ch), Set.Nonempty (Z i) ∧ IsCompact (Z i) ∧ IsClosed (Z i) := by
            intro X
            -- `Z X` nonempty
            simp
            have h₃ := (h (Subtype.mem X)).2
            rw [←image_inter_nonempty_iff, h₃]
            simp
            -- `Z X` is Closed
            have := (h (Subtype.mem X)).1
            have h_cl := IsClosed.inter this (IsClosed.preimage π_cont <| T1Space.t1 x)
            exact And.intro (IsClosed.isCompact h_cl) h_cl
          apply IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed Z _
              (fun X => (assumps X).1) (fun X => (assumps X).2.1) (fun X => (assumps X).2.2)
        -- Need to show the `Directed` assumption for the inclusion, which is annoying...
          change Directed _ ((fun X => X ∩ _) ∘ (fun X => X: ↑Ch → Set (D)))
          refine' Directed.mono_comp _ _ _
          · exact fun x y => x ⊇ y
          · exact fun ⦃x y⦄ a => inter_subset_inter_left _ a
          refine Iff.mp directedOn_iff_directed ?_
          refine IsChain.directedOn ?H
          dsimp [IsChain, Pairwise] at hCh ⊢
          exact fun ⦃x⦄ a ⦃y⦄ a_1 a_2 =>  Or.comm.mp (hCh a a_1 a_2)
    · intro X hX
      exact sInter_subset_of_mem hX
  have := zorn_superset S chain_cond
  rcases this with ⟨E, ⟨⟨hE₁,hE₂⟩, hE₃⟩⟩
  use E
  constructor
  · exact isCompact_iff_compactSpace.mp hE₁.isCompact
  constructor
  · exact hE₂
  --Now, it's just rephrasing the conclusion of Zorn's Lemma
  · intro E₀ h₁ h₂
    replace hE₃ := hE₃ E₀
    by_contra h₃
    replace hE₃ := hE₃ (And.intro (h2 h₂) (h3 h₃)) (subset_of_ssubset (h1 h₁))
    exact (ne_of_ssubset (h1 h₁)) hE₃

/-- Theorem 2.5 (Gleason) -/
instance [T2Space A] [CompactSpace A] [ExtremallyDisconnected A] : CompactT2.Projective A := by
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  let D : Set <| A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  let π₁ : D → A := Prod.fst ∘ Subtype.val
  have π₁_cont : Continuous π₁ := continuous_fst.comp continuous_subtype_val
  have π₁_surj : π₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_image_ne_top π₁_cont π₁_surj with ⟨E, _, E_surj, E_proper⟩
  let ρ : E → A := E.restrict π₁
  have ρ_cont : Continuous ρ := π₁_cont.continuousOn.restrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_surj ▸ Set.mem_univ a : a ∈ π₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := compact_to_T2_homeomorph ρ_cont ρ_surj E_proper
  let π₂ : D → B := Prod.snd ∘ Subtype.val
  have π₂_cont : Continuous π₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.restrict π₂ ∘ ρ'.symm, ⟨π₂_cont.continuousOn.restrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.restrict π₂ = φ ∘ ρ' by
    rw [← comp.assoc, this, comp.assoc, Homeomorph.self_comp_symm, comp.right_id]
  ext x
  exact x.val.property.symm
