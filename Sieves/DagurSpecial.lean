import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import ExtrDisc.Coherent
import Sieves.isSheafForPullbackSieve

universe u

section Coverage
namespace CategoryTheory

open CategoryTheory.Limits

def DagurSieveIso (B : ExtrDisc) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → ExtrDisc)
  (π : (a : α) → (X a ⟶ B)), S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def DagurSieveSingle (B : ExtrDisc) := { S | ∃ (X : ExtrDisc) (f : X ⟶ B), 
    S = Presieve.ofArrows (fun (_ : Unit) ↦ X) (fun (_ : Unit) ↦ f) ∧ Epi f }

lemma clopen_extremallyDisconnected {X : ExtrDisc} {U : Set X} (hU : IsClopen U) :
    ExtremallyDisconnected U := by
  constructor
  intro V hV
  have hV' : IsOpen (Subtype.val '' V) := hU.1.openEmbedding_subtype_val.isOpenMap V hV
  have := ExtremallyDisconnected.open_closure _ hV'
  rw [hU.2.closedEmbedding_subtype_val.closure_image_eq V] at this 
  suffices hhU : closure V = Subtype.val ⁻¹' (Subtype.val '' (closure V)) 
  · rw [hhU]
    exact isOpen_induced this 
  exact ((closure V).preimage_image_eq Subtype.coe_injective).symm 

def OpenEmbeddingConePt {X Y Z : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) : 
    ExtrDisc where
  compHaus := {
    toTop := TopCat.of (f ⁻¹' (Set.range i))
    is_compact := by
      dsimp [TopCat.of]
      rw [← isCompact_iff_compactSpace] 
      apply IsClosed.isCompact 
      refine' IsClosed.preimage f.continuous _ 
      apply IsCompact.isClosed 
      simp only [← Set.image_univ]
      exact IsCompact.image isCompact_univ i.continuous 
    is_hausdorff := by
      dsimp [TopCat.of]
      exact inferInstance
  }
  extrDisc := by
    constructor 
    have h : IsClopen (f ⁻¹' (Set.range i))
    · constructor
      · exact IsOpen.preimage f.continuous hi.open_range
      · refine' IsClosed.preimage f.continuous _ 
        apply IsCompact.isClosed 
        simp only [← Set.image_univ]
        exact IsCompact.image isCompact_univ i.continuous 
    intro U hU 
    dsimp at U 
    have hU' : IsOpen (Subtype.val '' U) := h.1.openEmbedding_subtype_val.isOpenMap U hU
    have := ExtremallyDisconnected.open_closure _ hU'
    rw [h.2.closedEmbedding_subtype_val.closure_image_eq U] at this 
    suffices hhU : closure U = Subtype.val ⁻¹' (Subtype.val '' (closure U)) 
    · rw [hhU]
      exact isOpen_induced this 
    exact ((closure U).preimage_image_eq Subtype.coe_injective).symm 

noncomputable
def OpenEmbeddingCone {X Y Z : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) : 
    Cone (cospan f i) where
  pt := OpenEmbeddingConePt f hi
  π := {
    app := by
      intro W 
      dsimp 
      match W with 
      | none => 
        exact ⟨Set.restrict _ f, ContinuousOn.restrict (Continuous.continuousOn f.continuous)⟩
      | some W' => 
        · induction W' with 
        | left => 
          · exact ⟨Subtype.val, continuous_subtype_val⟩ 
        | right => 
          · sorry
    naturality := sorry
  }

lemma HasPullbackOpenEmbedding {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : HasPullback f i := by
  constructor
  use OpenEmbeddingCone f hi 
  constructor
  · sorry 
  · sorry 
  · sorry 

def dagurCoverageExtrDisc : Coverage ExtrDisc where
  covering B := (DagurSieveIso B) ∪ (DagurSieveSingle B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · have : ∀ a : α, OpenEmbedding (π a)
      · sorry
      haveI hpb : ∀ a : α, HasPullback f (π a) := fun a ↦ HasPullbackOpenEmbedding f (this a)  
      set Z' : α → ExtrDisc := fun a ↦ pullback f (π a) with hZ'
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows ExtrDisc _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [DagurSieveIso]
        simp only [Set.mem_setOf_eq]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          have := @Limits.pullback_snd_iso_of_right_iso ExtrDisc _ Y (∐ fun b => Z b) X f 
            (Sigma.desc π) h_iso
          have hdo : OpenEmbedding (Sigma.desc π)
          · sorry
          haveI hpbd : HasPullback f (Sigma.desc π) := HasPullbackOpenEmbedding f hdo
          let ψ : Limits.pullback f (Sigma.desc π) ⟶ Y := pullback.fst
          let φ : (∐ fun b => Z' b) ⟶ Limits.pullback f (Sigma.desc π)
          · sorry
          have aux : IsIso φ
          · sorry
          have comp : φ ≫ ψ = Sigma.desc fun a => pullback.fst
          · sorry
          rw [← comp]
          infer_instance
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩-- with a
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · sorry

lemma isPullbackSieve_DagurSieveIso {X : ExtrDisc} {S : Presieve X}
    (hS : S ∈ DagurSieveIso X) : isPullbackPresieve S := by
  intro _ _ _ _ g hg 
  refine' HasPullbackOpenEmbedding _ _
  dsimp [DagurSieveIso] at hS
  obtain ⟨α, x, Xmap, π, hS⟩ := hS 
  rw [hS.1] at hg 
  induction hg with 
  | mk i => 
    · have h₁ : OpenEmbedding (Sigma.desc π)
      · sorry
        -- let h := (homeoOfIso (@asIso _ _ _ _ (Sigma.desc π) hS.2))
      have h₂ : OpenEmbedding (Sigma.ι Xmap i)
      · constructor
        · sorry
        · sorry-- rw [isOpen_sigma_iff]
      have := OpenEmbedding.comp h₁ h₂ 
      erw [← CategoryTheory.coe_comp (Sigma.ι Xmap i) (Sigma.desc π)] at this 
      simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at this 
      assumption 
  
    
lemma isSheafForDagurSieveIso {X : ExtrDisc} {S : Presieve X} (hS : S ∈ DagurSieveIso X)
    {F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)} (hF : PreservesFiniteProducts F) : 
    Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_DagurSieveIso hS).2 _
  sorry

end CategoryTheory

end Coverage