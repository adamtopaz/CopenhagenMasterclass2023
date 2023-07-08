import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Homeomorph

open Function Set

section

variable {A : Type u} {B : Set A} {C : Set B}

private lemma mem_coe_of_mem {a : A} (ha : a ∈ B) (ha' : ⟨a, ha⟩ ∈ C) : a ∈ (C : Set A) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩

private lemma coe_subset : (C : Set A) ⊆ B := by
  rintro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert ha

private lemma mem_of_mem_coe {a : A} (ha : a ∈ (C : Set A)) : ⟨a, coe_subset ha⟩ ∈ C := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert ha

private lemma eq_univ_of_coe_eq (hC : (C : Set A) = B) : C = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe <| hC.symm ▸ ha

private lemma IsClosed.trans [TopologicalSpace A] (hC : IsClosed C) (hB : IsClosed B) :
    IsClosed (C : Set A) := by
  rcases isClosed_induced_iff.mp hC with ⟨D, hD, rfl⟩
  convert IsClosed.inter hB hD
  ext
  exact ⟨fun h => ⟨coe_subset h, mem_of_mem_coe h⟩, fun ⟨hB, hD⟩ => mem_coe_of_mem hB hD⟩

private lemma image_coe_eq_restrict_image {f : A → E} : f '' C = B.restrict f '' C :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

private lemma not_nonempty_iff_eq_empty : ¬Nonempty B ↔ B = ∅ := by
  rw [nonempty_subtype, not_exists, eq_empty_iff_forall_not_mem]

private lemma nonempty_iff_ne_empty : Nonempty B ↔ B ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right

end

variable {A B C D : Type u} {E : Set D}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/-- Gleason's Lemma 2.1: if $\rho$ is a continuous surjection from a topological space $E$ to a
topological space $A$ satisfying the "Zorn subset condition", then $\rho(G)$ is contained in the
closure of $A \setminus \rho(E \setminus G)}$ for any open set $G$ of $E$. -/
lemma image_subset_closure_compl_image_compl_of_isOpen {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ)
    {G : Set E} (hG : IsOpen G) : ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  by_cases G_empty : G = ∅
  · simpa only [G_empty, image_empty] using empty_subset _
  · intro a ha
    rw [mem_closure_iff]
    intro N N_open hN
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    have nonempty : (G ∩ ρ⁻¹' N).Nonempty := ⟨e, mem_inter he <| mem_preimage.mpr hN⟩
    have is_open : IsOpen <| G ∩ ρ⁻¹' N := hG.inter <| N_open.preimage ρ_cont
    have ne_univ : ρ '' (G ∩ ρ⁻¹' N)ᶜ ≠ univ := zorn_subset _ (compl_ne_univ.mpr nonempty)
                                                  is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := (compl_subset_compl.mpr <| image_subset ρ <|
                                    compl_subset_compl.mpr <| G.inter_subset_left _) hx
    rcases ρ_surj x with ⟨y, rfl⟩
    have hy : y ∈ G ∩ ρ⁻¹' N := not_mem_compl_iff.mp <| (not_imp_not.mpr <| mem_image_of_mem ρ) <|
                                  (mem_compl_iff _ _).mp hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

/-- Gleason's Lemma 2.2: in an extremally disconnected space, if $U_1$ and $U_2$ are disjoint open
sets, then $\overline{U_1}$ and $\overline{U_2}$ are also disjoint. -/
lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_IsOpen [ExtremallyDisconnected A]
    {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) :
    Disjoint (closure U₁) (closure U₂) :=
  (h.closure_right hU₁).closure_left <| open_closure U₂ hU₂

private lemma ExtremallyDisconnected.homeoCompactToT2_injective [ExtremallyDisconnected A]
    [T2Space A] [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) :
    ρ.Injective := by
  intro x₁ x₂ hρx
  by_contra hx
  rcases t2_separation hx with ⟨G₁, G₂, G₁_open, G₂_open, hx₁, hx₂, disj⟩
  have G₁_comp : IsCompact <| G₁ᶜ := IsClosed.isCompact G₁_open.isClosed_compl
  have G₂_comp : IsCompact <| G₂ᶜ := IsClosed.isCompact G₂_open.isClosed_compl
  have G₁_open' : IsOpen ((ρ '' G₁ᶜ)ᶜ) := (G₁_comp.image ρ_cont).isClosed.isOpen_compl
  have G₂_open' : IsOpen ((ρ '' G₂ᶜ)ᶜ) := (G₂_comp.image ρ_cont).isClosed.isOpen_compl
  have disj' : Disjoint ((ρ '' G₁ᶜ)ᶜ) ((ρ '' G₂ᶜ)ᶜ) := by
    rw [disjoint_iff_inter_eq_empty, ← compl_union, ← image_union, ← compl_inter,
      disjoint_iff_inter_eq_empty.mp disj, compl_empty, compl_empty_iff,
      image_univ_of_surjective ρ_surj]
  have disj'' : Disjoint (closure <| (ρ '' G₁ᶜ)ᶜ) (closure <| (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_IsOpen disj' G₁_open' G₂_open'
  have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open <|
    mem_image_of_mem ρ hx₁
  have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open <|
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx

/-- Gleason's Lemma 2.3: a continuous surjection from a compact Hausdorff space to an extremally
disconnected Hausdorff space satisfying the "Zorn subset condition" is a homeomorphism. -/
noncomputable def ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Space A]
    [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
    (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) : E ≃ₜ A :=
  ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

/-- Gleason's Lemma 2.4: a continuous surjection $\rho$ from a compact space $D$ to a Fréchet space
$A$ restricts to a compact subset $E$ of $D$, such that $\rho$ maps $E$ onto $A$ and satisfies the
"Zorn subset condition", where $\rho(E_0) \ne A$ for any proper closed subset $E_0 \subsetneq E$. -/
lemma exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {π : D → A}
    (π_cont : Continuous π) (π_surj : π.Surjective) : ∃ E : Set D, CompactSpace E ∧ π '' E = univ ∧
    ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → E.restrict π '' E₀ ≠ univ := by
  let S : Set <| Set D := {E : Set D | IsClosed E ∧ π '' E = univ}
  suffices ∀ (C : Set <| Set D) (_ : C ⊆ S) (_ : IsChain (· ⊆ ·) C), ∃ s ∈ S, ∀ c ∈ C, s ⊆ c by
    rcases zorn_superset S this with ⟨E, ⟨E_closed, E_surj⟩, E_min⟩
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose! E₀_min
    exact eq_univ_of_coe_eq <|
      E_min E₀ ⟨E₀_closed.trans E_closed, image_coe_eq_restrict_image ▸ E₀_min⟩ coe_subset
  intro C C_sub C_chain
  refine ⟨iInter (fun c : C => c), ⟨isClosed_iInter fun ⟨_, h⟩ => (C_sub h).left, ?_⟩,
    fun c hc _ h => mem_iInter.mp h ⟨c, hc⟩⟩
  by_cases hC : Nonempty C
  · refine eq_univ_of_forall fun a => inter_nonempty_iff_exists_left.mp ?_
    refine iInter_inter (ι := C) (π ⁻¹' {a}) _ ▸
      IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed _
      ?_ (fun c => ?_) (fun c => IsClosed.isCompact ?_) (fun c => ?_)
    · replace C_chain : IsChain (· ⊇ ·) C := C_chain.symm
      have : ∀ s t : Set D, s ⊇ t → _ ⊇ _ := fun _ _ => inter_subset_inter_left <| π ⁻¹' {a}
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (· ⊇ ·) this
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
    all_goals exact (C_sub c.mem).left.inter <| (T1Space.t1 a).preimage π_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective π_surj]

/-- Gleason's Theorem 2.5: in the category of compact spaces and continuous maps, the
projective spaces are precisely the extremally disconnected spaces. -/
protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
    [CompactSpace A] [T2Space A] : CompactT2.Projective A := by
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  let D : Set <| A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  let π₁ : D → A := Prod.fst ∘ Subtype.val
  have π₁_cont : Continuous π₁ := continuous_fst.comp continuous_subtype_val
  have π₁_surj : π₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset π₁_cont π₁_surj with ⟨E, _, E_onto, E_min⟩
  let ρ : E → A := E.restrict π₁
  have ρ_cont : Continuous ρ := π₁_cont.continuousOn.restrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a ∈ π₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  let π₂ : D → B := Prod.snd ∘ Subtype.val
  have π₂_cont : Continuous π₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.restrict π₂ ∘ ρ'.symm, ⟨π₂_cont.continuousOn.restrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.restrict π₂ = φ ∘ ρ' by
    rw [← comp.assoc, this, comp.assoc, Homeomorph.self_comp_symm, comp.right_id]
  ext x
  exact x.val.mem.symm
