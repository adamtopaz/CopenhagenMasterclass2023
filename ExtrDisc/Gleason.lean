import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Homeomorph

variable {A B C D : Type _} {E : Set D} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace C] [TopologicalSpace D]
  {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
  {π : D → A} (π_cont : Continuous π) (π_surj : π.Surjective)
  (image_ne_top : ∀ E₀ : Set E, E₀ ≠ ⊤ → IsClosed E₀ → ρ '' E₀ ≠ ⊤)

open Set

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

variable [T2Space A] [CompactSpace A] [T2Space B] [CompactSpace B] [T2Space C] (φ : A → C) (f : B → C)

def D' : Set (A × B) := {x | φ x.fst = f x.snd}

def π₁ : D' φ f → A := fun x ↦ x.val.fst

def π₂ : D' φ f → B := fun x ↦ x.val.snd

variable {φ f} (hφ : Continuous φ) (hf : Continuous f) (hf' : f.Surjective)

/-- Lemma 2.4 -/
lemma exists_image_ne_top : ∃ E : Set <| D' φ f, CompactSpace E ∧ π₁ φ f '' E = univ ∧
    ∀ E₀ : Set <| D' φ f, E₀ ⊂ E → CompactSpace E₀ → π₁ φ f '' E₀ ≠ univ := by
  haveI : CompactSpace <| D' φ f := isCompact_iff_compactSpace.mp (IsClosed.isCompact
    (isClosed_eq (Continuous.comp hφ continuous_fst) (Continuous.comp hf continuous_snd)))
  -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set (D' φ f) | CompactSpace E ∧ (π₁ φ f) '' E = univ}
  -- Checking the Chain condition
  have chain_cond : (∀ (c : Set (Set ↑(D' φ f))),
      c ⊆ S →
      IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D' φ f)), s ∈ c → lb ⊆ s) := by
    intro Ch h hCh
    let M := sInter Ch
    use M
    constructor
    · constructor
      · rw [←isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        apply isClosed_sInter
        intro N hN
        have N_comp := (h hN).1
        dsimp at N_comp
        rw [←isCompact_iff_compactSpace] at N_comp
        exact IsCompact.isClosed N_comp
      --Next, we need to show that the image of M is all of A
      · by_cases h₂ : Nonempty Ch
        rotate_left 1
        -- Case that `Ch` is empty
        · simp at h₂
          rw [←eq_empty_iff_forall_not_mem] at h₂
          revert M
          rw [h₂, sInter_empty]
          simp
          exact range_iff_surjective.mpr <| fun a => ⟨⟨⟨_, _⟩, (hf' <| φ a).choose_spec.symm⟩, rfl⟩
        -- Now we assume that `Ch` is nonempty
        · ext x
          refine' ⟨ fun _ => trivial , fun _ => _ ⟩
          rw [mem_image]
          change Set.Nonempty {x_1 : D' φ f | x_1 ∈ M ∧ π₁ φ f x_1 = x}
          let Z : Ch → Set (D' φ f) := fun X => X ∩ (π₁ _ _)⁻¹' {x}
          suffices Set.Nonempty <| ⋂ (X : Ch), (X: Set (D' φ f)) ∩ (π₁ _ _)⁻¹' {x} by
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
            rw [←isCompact_iff_compactSpace] at this
            have h_cl := IsClosed.inter (IsCompact.isClosed this)
                (IsClosed.preimage (Continuous.comp continuous_fst continuous_subtype_val) <| T1Space.t1 x)
            exact And.intro (IsClosed.isCompact h_cl) h_cl

          apply IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed Z _
              (fun X => (assumps X).1) (fun X => (assumps X).2.1) (fun X => (assumps X).2.2)
        -- Need to show the `Directed` assumption for the inclusion, which is annoying...
          change Directed _ ((fun X => X ∩ _) ∘ (fun X => X: ↑Ch → Set (D' φ f)))
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
  · exact hE₁
  constructor
  · exact hE₂
  --Now, it's just rephrasing the conclusion of Zorn's Lemma
  · intro E₀ h₁ h₂
    replace hE₃ := hE₃ E₀
    by_contra h₃
    replace hE₃ := hE₃ (And.intro h₂ h₃) (subset_of_ssubset h₁)
    exact (ne_of_ssubset h₁) hE₃

def E' [T2Space A] [CompactSpace A] : Set <| D' φ f := (exists_image_ne_top hφ hf hf').choose

noncomputable def ρ' [ExtremallyDisconnected A] : (E' hφ hf hf') ≃ₜ A := by
  haveI : CompactSpace <| E' hφ hf hf' := (exists_image_ne_top hφ hf hf').choose_spec.1
  have π₁_surj : ((E' hφ hf hf').restrict (π₁ φ f)).Surjective := by
    intro a
    have := (exists_image_ne_top hφ hf hf').choose_spec.2.1
    have ha : a ∈ univ := by tauto
    rw [← this] at ha
    obtain ⟨c,hc⟩ := ha
    use ⟨c,hc.1⟩
    exact hc.2
  have π₁_cont : Continuous ((E' hφ hf hf').restrict (π₁ φ f)) :=
    ContinuousOn.restrict (Continuous.continuousOn (Continuous.comp continuous_fst continuous_subtype_val))
  refine' compact_to_T2_homeomorph π₁_cont π₁_surj _
  have := (exists_image_ne_top hφ hf hf').choose_spec.2.2
  simp_rw [top_eq_univ, ← ne_eq, ← ssubset_univ_iff]
  intro E₀ hE₀ hE₀c
  let E₀' : Set (D' φ f) := Subtype.val '' E₀
  have hE₀' : E₀' ⊂ E' hφ hf hf'
  · rw [ssubset_iff_subset_ne]
    constructor
    · intro x hx
      dsimp at hx
      obtain ⟨y,hy⟩ := hx
      rw [← hy.2]
      exact y.prop
    · rw [ssubset_iff_subset_ne] at hE₀
      dsimp
      intro h
      apply hE₀.2
      ext x
      refine' ⟨by tauto, _⟩
      intro _
      have hx := x.prop
      simp_rw [← h] at hx
      obtain ⟨y,hy⟩ := hx
      have hxy : y = x
      · ext1
        exact hy.2
      rw [← hxy]
      exact hy.1
  specialize this E₀' hE₀'
  rw [ssubset_univ_iff]
  have hE₀c' : CompactSpace E₀'
  · rw [← isCompact_iff_compactSpace]
    haveI : CompactSpace <| D' φ f := isCompact_iff_compactSpace.mp (IsClosed.isCompact
      (isClosed_eq (Continuous.comp hφ continuous_fst) (Continuous.comp hf continuous_snd)))
    apply IsClosed.isCompact
    dsimp
    refine Iff.mp (ClosedEmbedding.closed_iff_image_closed ?hE₀c'.h.hf) hE₀c
    apply closedEmbedding_subtype_val
    apply IsCompact.isClosed
    rw [isCompact_iff_compactSpace]
    exact (exists_image_ne_top hφ hf hf').choose_spec.1
  have hπ : (E' hφ hf hf').restrict (π₁ φ f) '' E₀ = π₁ φ f '' E₀'
  · simp only [restrict_apply]
    ext a
    simp only [mem_image, Subtype.exists, exists_and_right, Prod.exists, exists_eq_right]
  specialize this hE₀c'
  rwa [hπ]

lemma gleason_diagram_commutes [ExtremallyDisconnected A] :
    Continuous ((E' hφ hf hf').restrict (π₂ φ f) ∘ (ρ' hφ hf hf').invFun) ∧
    f ∘ ((E' hφ hf hf').restrict (π₂ φ f) ∘ (ρ' hφ hf hf').invFun) = φ := by
  constructor
  · refine' Continuous.comp _ _
    · refine' ContinuousOn.restrict _
      apply Continuous.continuousOn
      exact Continuous.comp continuous_snd continuous_subtype_val
    · exact (Homeomorph.continuous (Homeomorph.symm (ρ' hφ hf hf')))
  · suffices : f ∘ (E' hφ hf hf').restrict (π₂ φ f) = φ ∘ (ρ' hφ hf hf').toFun
    · simp only [← Function.comp.assoc]
      rw [this]
      simp only [Function.comp.assoc, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv,
        Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv,
        Homeomorph.self_comp_symm, Function.comp.right_id]
    ext x
    simp only [Function.comp_apply, restrict_apply, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv]
    dsimp [π₂, ρ', compact_to_T2_homeomorph, Continuous.homeoOfEquivCompactToT2_toEquiv,
      Continuous.homeoOfEquivCompactToT2, π₁]
    have := x.val.prop
    dsimp [D'] at this
    exact this.symm
