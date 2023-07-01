import ExtrDisc.Basic
import ExtrDisc.Coherent
import Mathlib.CategoryTheory.Sites.Sheaf
import Sieves.isSheafForPullbackSieve
import Sieves.dagur
import Sieves.OpenEmbedding

universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits Functor Presieve

namespace ExtrDisc

def homeoOfIso {X Y : ExtrDisc} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := by
    intro x 
    have : f.inv (f.hom x) = (f.hom ≫ f.inv) x
    · rfl 
    rw [this]
    simp only [Iso.hom_inv_id]
    rfl
  right_inv := by
    intro x 
    have : f.hom (f.inv x) = (f.inv ≫ f.hom) x
    · rfl 
    rw [this]
    simp only [Iso.inv_hom_id]
    rfl
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

end ExtrDisc

namespace CategoryTheory

open CategoryTheory.Limits

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

lemma pullback.lift_snd {X Y Z W : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) : 
    pullback.lift f hi a b w ≫ ExtrDisc.pullback.snd f hi = b := by 
  dsimp [lift, snd, OpenEmbeddingCone, OpenEmbeddingConeRightMap, ContinuousMap.comp, Set.restrict, 
    Set.codRestrict, OpenEmbedding.InvRange]
  congr 
  ext z
  simp only [Function.comp_apply]
  have := congr_fun (FunLike.ext'_iff.mp w.symm) z 
  have h : i (b z) = f (a z) := this
  suffices : b z = (Homeomorph.ofEmbedding i hi.toEmbedding).symm 
    (⟨f (a z), by rw [← h] ; simp⟩) 
  · exact this.symm
  apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
  simp only [Homeomorph.apply_symm_apply]
  dsimp [Homeomorph.ofEmbedding]
  simp_rw [h]

lemma pullback.hom_ext {X Y Z W : ExtrDisc} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ (OpenEmbeddingCone f hi).pt) (b : W ⟶ (OpenEmbeddingCone f hi).pt)
    (hfst : a ≫ pullback.fst f hi = b ≫ pullback.fst f hi) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst--  hsnd
  apply Subtype.ext
  exact hfst


def OpenEmbeddingLimitCone {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : IsLimit (OpenEmbeddingCone f hi) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f hi s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm WalkingCospan.left))

lemma HasPullbackOpenEmbedding {X Y Z : ExtrDisc.{u}} (f : X ⟶ Z) {i : Y ⟶ Z} 
    (hi : OpenEmbedding i) : HasPullback f i := by
  constructor
  use OpenEmbeddingCone f hi 
  exact ExtrDisc.OpenEmbeddingLimitCone f hi

instance : HasPullbackOfIsIsodesc ExtrDisc := by
  constructor 
  intro X Z α f Y i _ _ _ a 
  apply HasPullbackOpenEmbedding 
  have h₁ : OpenEmbedding (Sigma.desc i) :=
    (ExtrDisc.homeoOfIso (asIso (Sigma.desc i))).openEmbedding
  have h₂ : OpenEmbedding (Sigma.ι Y a) := DagurOpenEmbedding _ _
  have := OpenEmbedding.comp h₁ h₂ 
  erw [← CategoryTheory.coe_comp (Sigma.ι Y a) (Sigma.desc i)] at this 
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at this 
  assumption

end ExtrDisc

end CategoryTheory