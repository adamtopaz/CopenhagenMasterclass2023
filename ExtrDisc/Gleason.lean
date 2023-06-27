import ExtrDisc.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.Zorn

open CategoryTheory Set

variable {A : Type _} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ExtremallyDisconnected A]
variable {B C : Type _} [TopologicalSpace B] [TopologicalSpace C] [T2Space B] [T2Space C]
  [CompactSpace B] [CompactSpace C]
variable (φ : A → C) (f : B → C)

def D : Set (A × B) := {x | φ x.fst = f x.snd}

def π₁ : D φ f → A := fun x ↦ x.val.fst

def π₂ : D φ f → B := fun x ↦ x.val.snd

variable {φ} {f} (hφ : Continuous φ) (hf : Continuous f) (hf' : f.Surjective)

instance one : CompactSpace (D φ f) :=
isCompact_iff_compactSpace.mp (IsClosed.isCompact
  (isClosed_eq (Continuous.comp hφ continuous_fst) (Continuous.comp hf continuous_snd )))

lemma two : (π₁ φ f).Surjective := by
  intro a
  obtain ⟨b, hb⟩ := hf' (φ a)
  use ⟨(a,b), hb.symm⟩
  rfl

lemma two_half : Continuous (π₁ φ f) := Continuous.comp continuous_fst continuous_subtype_val

lemma three : ∃ (E : Set (D φ f)), CompactSpace E ∧ (π₁ φ f) '' E = univ ∧ ∀ (E₀ : Set (D φ f)),
    E₀ ⊂ E → CompactSpace E₀ → ¬ ((π₁ φ f)'' E₀) = univ := by
  -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set (D φ f) | CompactSpace E ∧ (π₁ φ f) '' E = univ}
  -- Checking the Chain condition
  have chain_cond : (∀ (c : Set (Set ↑(D φ f))),
      c ⊆ S →
      IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D φ f)), s ∈ c → lb ⊆ s) := by
    intro Ch h hCh
    let M := sInter Ch
    use M
    constructor
    · constructor
      · rw [←isCompact_iff_compactSpace]
        apply @IsClosed.isCompact _ _ (one hφ hf)
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
          exact Iff.mpr range_iff_surjective (two hf')
        -- Now we assume that `Ch` is nonempty
        · ext x
          refine' ⟨ fun _ => trivial , fun _ => _ ⟩
          rw [mem_image]
          change Set.Nonempty {x_1 : D φ f | x_1 ∈ M ∧ π₁ φ f x_1 = x}
          let Z : Ch → Set (D φ f) := fun X => X ∩ (π₁ _ _)⁻¹' {x}
          suffices Set.Nonempty <| ⋂ (X : Ch), (X: Set (D φ f)) ∩ (π₁ _ _)⁻¹' {x} by
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
                (IsClosed.preimage two_half <| T1Space.t1 x)
            exact And.intro (@IsClosed.isCompact _ _ (one hφ hf) _ h_cl) h_cl

          apply IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed Z _
              (fun X => (assumps X).1) (fun X => (assumps X).2.1) (fun X => (assumps X).2.2)
        -- Need to show the `Directed` assumption for the inclusion, which is annoying...
          change Directed _ ((fun X => X ∩ _) ∘ (fun X => X: ↑Ch → Set (D φ f)))
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


def E : (Set (D φ f)) := (three hφ hf hf').choose

lemma gleason21 (A E : Type _) [TopologicalSpace A] [TopologicalSpace E] [T2Space A] [T2Space E]
  {ρ : E → A} (ρ_cts : Continuous ρ) (ρ_surj : ρ.Surjective) (zorn : ∀ E₀ : Set E, E₀ ≠ ⊤ →
  IsClosed E₀ → ρ '' E₀ ≠ ⊤) {G : Set E} (G_open : IsOpen G) : ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  by_cases G_empty : G = ∅
  · simpa only [G_empty, image_empty] using empty_subset _
  · intro a ha
    rw [mem_closure_iff]
    intro N N_open ha'
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    have non_empty : Set.Nonempty (G ∩ ρ⁻¹' N) := ⟨e, mem_inter he <| mem_preimage.mpr ha'⟩
    have is_open : IsOpen <| G ∩ ρ⁻¹' N := G_open.inter <| N_open.preimage ρ_cts
    have ne_top : ρ '' (G ∩ ρ⁻¹' N)ᶜ ≠ ⊤ :=
      zorn _ (compl_ne_univ.mpr non_empty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_top with ⟨x, hx⟩
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := (compl_subset_compl.mpr <| image_subset ρ <|
                                    compl_subset_compl.mpr <| G.inter_subset_left _) hx
    rcases ρ_surj x with ⟨y, rfl⟩
    have hy : y ∈ G ∩ ρ⁻¹' N := not_mem_compl_iff.mp <| (not_imp_not.mpr <| mem_image_of_mem ρ) <|
                                  (mem_compl_iff _ _).mp hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

lemma gleason22 {E₁ E₂ : Set A} (h : Disjoint E₁ E₂) (h₁ : IsOpen E₁) (h₂ : IsOpen E₂) :
    Disjoint (closure E₁) (closure E₂) :=
  Disjoint.closure_left (Disjoint.closure_right h h₁) (ExtremallyDisconnected.open_closure E₂ h₂)

lemma gleason23_inj (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
  (hr_surj: r.Surjective) (hE : CompactSpace E)
  (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) : r.Injective := by
  · rw [Function.Injective]
    intros x y h_eq_im
    by_contra h
    rcases t2_separation h with ⟨G₁, G₂, hG₁, hG₂, hxG₁, hyG₂, hG⟩
    have open1 : IsOpen ((r '' (G₁ᶜ))ᶜ)
    · simp only [isOpen_compl_iff]
      apply IsCompact.isClosed
      refine' IsCompact.image (IsClosed.isCompact _) hr
      simpa only [isClosed_compl_iff]
    have open2 : IsOpen ((r '' (G₂ᶜ))ᶜ)
    · simp only [isOpen_compl_iff]
      apply IsCompact.isClosed
      refine' IsCompact.image (IsClosed.isCompact _) hr
      simpa only [isClosed_compl_iff]
    have disj : Disjoint ((r '' (G₁ᶜ))ᶜ) ((r '' (G₂ᶜ))ᶜ)
    · rw [disjoint_compl_left_iff_subset]
      refine' subset_trans (subset_image_compl hr_surj) _
      simp only [compl_compl, image_subset_iff]
      refine' subset_trans _ (subset_preimage_image _ _)
      rw [← disjoint_compl_left_iff_subset]
      simpa only [compl_compl]
    replace disj := gleason22 disj open1 open2
    have oups₁ := gleason21 A E hr hr_surj h_subsets hG₁
    have oups₂ := gleason21 A E hr hr_surj h_subsets hG₂
    have mem₁ : r x ∈ r '' G₁
    · exact mem_image_of_mem _ hxG₁
    have mem₂ : r x ∈ r '' G₂
    · rw [h_eq_im]
      exact mem_image_of_mem _ hyG₂
    have mem : r x ∈ (closure ((r '' G₁ᶜ)ᶜ)) ∩ (closure ((r '' G₂ᶜ)ᶜ)) := ⟨oups₁ mem₁, oups₂ mem₂⟩
    exact (disj.ne_of_mem mem.1 mem.2) rfl

lemma gleason23_surj : ((E hφ hf hf').restrict (π₁ φ f)).Surjective := by
  intro a
  have := (three hφ hf hf').choose_spec.2.1
  have ha : a ∈ univ := by tauto
  rw [← this] at ha
  obtain ⟨c,hc⟩ := ha
  use ⟨c,hc.1⟩
  exact hc.2

lemma gleason23_cont (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
    (hr_surj: r.Surjective) (hE : CompactSpace E)
    (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) :
    Continuous (Function.Embedding.equivOfSurjective
    ⟨r, gleason23_inj E hr hr_surj hE h_subsets⟩ hr_surj) := hr

lemma gleason23_cont' : Continuous ((E hφ hf hf').restrict (π₁ φ f)) :=
ContinuousOn.restrict (Continuous.continuousOn (Continuous.comp continuous_fst
  continuous_subtype_val))

noncomputable
def gleason23_def (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
  (hr_surj: r.Surjective) (hE : CompactSpace E)
  (h_subsets : ∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) : E ≃ₜ A :=
Continuous.homeoOfEquivCompactToT2 (gleason23_cont E hr hr_surj hE h_subsets)

noncomputable
def ρ : (E hφ hf hf') ≃ₜ A := by
  refine' gleason23_def (E hφ hf hf') (gleason23_cont' hφ hf hf') (gleason23_surj hφ hf hf')
    (three hφ hf hf').choose_spec.1 _
  have := (three hφ hf hf').choose_spec.2.2
  simp_rw [top_eq_univ, ← ne_eq, ← ssubset_univ_iff]
  intro E₀ hE₀ hE₀c
  let E₀' : Set (D φ f) := Subtype.val '' E₀
  have hE₀' : E₀' ⊂ E hφ hf hf'
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
    haveI CD : CompactSpace (D φ f) := one hφ hf
    apply IsClosed.isCompact
    dsimp
    refine Iff.mp (ClosedEmbedding.closed_iff_image_closed ?hE₀c'.h.hf) hE₀c
    apply closedEmbedding_subtype_val
    apply IsCompact.isClosed
    rw [isCompact_iff_compactSpace]
    exact (three hφ hf hf').choose_spec.1
  have hπ : (E hφ hf hf').restrict (π₁ φ f) '' E₀ = π₁ φ f '' E₀'
  · simp only [restrict_apply]
    ext a
    simp only [mem_image, Subtype.exists, exists_and_right, Prod.exists, exists_eq_right]
  specialize this hE₀c'
  rwa [hπ]

lemma five : Continuous ((E hφ hf hf').restrict (π₂ φ f) ∘ (ρ hφ hf hf').invFun) ∧
    f ∘ ((E hφ hf hf').restrict (π₂ φ f) ∘ (ρ hφ hf hf').invFun) = φ := by
  constructor
  · refine' Continuous.comp _ _
    · refine' ContinuousOn.restrict _
      apply Continuous.continuousOn
      exact Continuous.comp continuous_snd continuous_subtype_val
    · exact (Homeomorph.continuous (Homeomorph.symm (ρ hφ hf hf')))
  · suffices : f ∘ (E hφ hf hf').restrict (π₂ φ f) = φ ∘ (ρ hφ hf hf').toFun
    · simp only [← Function.comp.assoc]
      rw [this]
      simp only [Function.comp.assoc, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv,
        Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv,
        Homeomorph.self_comp_symm, Function.comp.right_id]
    ext x
    simp only [Function.comp_apply, restrict_apply, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv]
    dsimp [π₂, ρ, gleason23_def, Continuous.homeoOfEquivCompactToT2_toEquiv,
      Continuous.homeoOfEquivCompactToT2, π₁]
    have := x.val.prop
    dsimp [D] at this
    exact this.symm

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected A.compHaus.toTop := A.extrDisc
    have hf : f.1.Surjective
    · rwa [CompHaus.epi_iff_surjective] at *
    use ⟨_, (five φ.continuous f.continuous hf).left⟩
    ext
    exact congr_fun (five φ.continuous f.continuous hf).right _
