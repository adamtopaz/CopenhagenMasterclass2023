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
def OpenEmbedding.InvRange {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {i : X → Y}
    (hi : OpenEmbedding i) : C(Set.range i, X) where
  toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).invFun
  continuous_toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).symm.continuous

noncomputable
def OpenEmbedding.ToRange {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {i : X → Y}
    (hi : OpenEmbedding i) : C(X, Set.range i) where
  toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).toFun
  continuous_toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).continuous

lemma aux_forall_mem {X Y Z : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (_ : OpenEmbedding i) : 
    ∀ x : f ⁻¹' (Set.range i), f x.val ∈ Set.range i := by
  rintro ⟨x, hx⟩ 
  simpa only [Set.mem_preimage]

lemma aux_continuous_restrict {X Y Z : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (_ : OpenEmbedding i) : 
    Continuous ((f ⁻¹' (Set.range i)).restrict f) := by
  apply ContinuousOn.restrict 
  apply Continuous.continuousOn 
  exact f.continuous

noncomputable
def OpenEmbeddingConeRightMap {X Y Z : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) :
    C(f ⁻¹' (Set.range i), Y) := 
  ContinuousMap.comp (OpenEmbedding.InvRange hi) 
  ⟨(Set.range i).codRestrict ((f ⁻¹' (Set.range i)).restrict f) 
  (aux_forall_mem f hi), Continuous.codRestrict 
  (aux_continuous_restrict f hi) (aux_forall_mem f hi)⟩  
  
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
          · exact OpenEmbeddingConeRightMap f hi
    naturality := by
      intro W V q
      simp only [Functor.const_obj_obj, Functor.const_obj_map, cospan_one, 
        cospan_left, id_eq, Category.id_comp]
      induction q with
      | id => 
        · simp only [cospan_one, cospan_left, WidePullbackShape.hom_id, 
          Functor.map_id, Category.comp_id]
      | term j => 
        · induction j with
          | left => 
            · simp only [cospan_one, cospan_left, cospan_map_inl]
              congr
          | right => 
            · simp only [cospan_one, cospan_right, cospan_map_inr]
              dsimp [OpenEmbeddingConeRightMap, ContinuousMap.comp, Set.restrict, Set.codRestrict,
                OpenEmbedding.InvRange]
              congr 
              ext x
              simp only [Function.comp_apply]
              obtain ⟨y, hy⟩ := x.prop 
              rw [← hy] 
              congr 
              suffices : y = (Homeomorph.ofEmbedding i hi.toEmbedding).symm 
                (⟨f x.val, by rw [← hy] ; simp⟩)
              · rw [this]
                rfl
              apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
              simp only [Homeomorph.apply_symm_apply]
              dsimp [Homeomorph.ofEmbedding]
              simp_rw [hy]
  }

namespace ExtrDisc

def pullback.fst {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : (OpenEmbeddingCone f hi).pt ⟶ X := 
  ⟨Subtype.val, continuous_subtype_val⟩ 

noncomputable
def pullback.snd {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : (OpenEmbeddingCone f hi).pt ⟶ Y := 
  (OpenEmbeddingCone f hi).π.app WalkingCospan.right

def pullback.lift {X Y Z W : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) : 
    W ⟶ (OpenEmbeddingCone f hi).pt where
  toFun := fun z => ⟨a z, by 
    simp only [Set.mem_preimage] 
    use (b z) 
    exact congr_fun (FunLike.ext'_iff.mp w.symm) z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk 
    exact a.continuous

@[reassoc (attr := simp)]
lemma pullback.lift_fst {X Y Z W : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) : 
  pullback.lift f hi a b w ≫ pullback.fst f hi = a := rfl

-- @[reassoc (attr := simp)]
lemma pullback.lift_snd {X Y Z W : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) : 
    pullback.lift f hi a b w ≫ ExtrDisc.pullback.snd f hi = b := by 
  dsimp [lift, snd, OpenEmbeddingCone, OpenEmbeddingConeRightMap, ContinuousMap.comp, Set.restrict, 
    Set.codRestrict, OpenEmbedding.InvRange]
  congr 
  ext z
  simp only [Function.comp_apply]
  sorry
  -- have := congr_fun (FunLike.ext'_iff.mp w.symm) z 
  -- obtain ⟨y, hy⟩ := x.prop 
  -- rw [← hy] 
  -- congr 
  -- suffices : y = (Homeomorph.ofEmbedding i hi.toEmbedding).symm 
  --   (⟨f x.val, by rw [← hy] ; simp⟩)
  -- · rw [this]
  --   rfl
  -- apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
  -- simp only [Homeomorph.apply_symm_apply]
  -- dsimp [Homeomorph.ofEmbedding]
  -- simp_rw [hy]
  -- have := (OpenEmbeddingCone f hi).π.naturality (𝟙 WalkingCospan.right)

-- lemma pullback.hom_ext {Z : CompHaus.{u}} (a b : Z ⟶ pullback f g)
--     (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
--     (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
--   ext z
--   apply_fun (fun q => q z) at hfst hsnd
--   apply Subtype.ext
--   apply Prod.ext
--   · exact hfst
--   · exact hsnd


def OpenEmbeddingLimitCone {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : IsLimit (OpenEmbeddingCone f hi) := sorry
  -- Limits.PullbackCone.isLimitAux _
  --   (fun s => pullback.lift f g s.fst s.snd s.condition)
  --   (fun _ => pullback.lift_fst _ _ _ _ _)
  --   (fun _ => pullback.lift_snd _ _ _ _ _)
  --   (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

end ExtrDisc

lemma HasPullbackOpenEmbedding {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : HasPullback f i := by
  constructor
  use OpenEmbeddingCone f hi 
  exact ExtrDisc.OpenEmbeddingLimitCone f hi


lemma ExtensivityExtrDisc {α : Type} {Y : ExtrDisc} [Fintype α]
   {Z : α → ExtrDisc}  {π : (a : α) → Z a ⟶ X} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)) 
  [∀ a : α, HasPullback f (π a)] :
  IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) := sorry


def dagurCoverageExtrDisc : Coverage ExtrDisc where
  covering B := (DagurSieveIso B) ∪ (DagurSieveSingle B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · have : ∀ a : α, OpenEmbedding (π a)
      · intro a
        have : π a = Sigma.ι Z a ≫ (Sigma.desc π)
        · simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
        rw [this]
        sorry
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
          apply ExtensivityExtrDisc
          exact h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (𝟙 Y) with hS'
      use S'
      constructor
      · apply Or.intro_right
        rw [DagurSieveSingle]
        simp only [Set.mem_setOf_eq]--comment
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        simp only [Category.id_comp]
        sorry

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