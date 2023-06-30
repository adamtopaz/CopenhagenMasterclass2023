import ExtrDisc.Basic
import ExtrDisc.Coherent
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Sieves.isSheafForPullbackSieve
import Sieves.dagur
import Sieves.OpenEmbedding

universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits Functor Presieve

section Coverage
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

-- @[reassoc (attr := simp)]
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

instance : HasPullbackOfRightMono ExtrDisc := by
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


lemma Extensivity_ExtrDisc : Extensivity ExtrDisc := sorry

lemma EverythingProj_ExtrDisc : EverythingIsProjective ExtrDisc := sorry

-- lemma Is_Mono_ι_ExtrDisc : IsMono_ι ExtrDisc := sorry

end ExtrDisc

end CategoryTheory

end Coverage

lemma one' : (dagurCoverage ExtrDisc EverythingProj_ExtrDisc
   Extensivity_ExtrDisc).toGrothendieck = 
    (coherentTopology ExtrDisc) := by
  ext X S  
  constructor
  <;> intro h 
  · dsimp [Coverage.toGrothendieck] at *
    induction h with 
    | of Y T hT => 
      · apply Coverage.saturate.of 
        dsimp [coherentCoverage]
        dsimp [dagurCoverage] at hT 
        apply Or.elim hT
        <;> intro h
        · obtain ⟨α, x, Xmap, π, h⟩ := h
          use α
          use x
          use Xmap 
          use π 
          refine' ⟨h.1,_⟩  
          have he := (effectiveEpiFamily_tfae Xmap π).out 0 1
          rw [he]
          letI := h.2
          exact inferInstance
        · obtain ⟨Z, f, h⟩ := h
          use Unit
          use inferInstance 
          use (fun _ ↦ Z) 
          use (fun _ ↦ f)
          refine' ⟨h.1,_⟩  
          have he := (effectiveEpiFamily_tfae (fun (_ : Unit) ↦ Z) (fun _ ↦ f)).out 0 1
          rw [he] 
          rw [ExtrDisc.epi_iff_surjective _] at h ⊢ 
          intro x 
          obtain ⟨y,hy⟩ := h.2 x  
          use Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit y 
          rw [← hy]
          suffices : (f : Z → Y) = Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit ≫ Sigma.desc (fun _ ↦ f)
          · rw [this]
            rfl
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]        
    | top => 
      · apply Coverage.saturate.top 
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption  
  · induction h with 
    | of Y T hT => 
      · dsimp [coherentCoverage] at hT 
        obtain ⟨I, hI, Xmap, f, ⟨h, hT⟩⟩ := hT     
        have he := (effectiveEpiFamily_tfae Xmap f).out 0 1
        rw [he] at hT 
        let φ := fun (i : I) ↦ Sigma.ι Xmap i
        let F := Sigma.desc f
        let Z := Sieve.generate T
        let Xs := (∐ fun (i : I) => Xmap i)
        let Zf : Sieve Y := Sieve.generate 
          (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F)) 
        apply Coverage.saturate.transitive Y Zf
        · apply Coverage.saturate.of 
          dsimp [dagurCoverage]
          simp only [Set.mem_union, Set.mem_setOf_eq]
          right
          use Xs 
          use F 
          refine' ⟨rfl, inferInstance⟩  
        · intro R g hZfg 
          dsimp at hZfg 
          rw [Presieve.ofArrows_pUnit] at hZfg
          obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg 
          dsimp [Presieve.singleton] at hW 
          induction hW
          rw [← hW', Sieve.pullback_comp Z]
          suffices : Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
            (dagurCoverage _ _ _).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (dagurCoverage _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [dagurCoverage] 
            left
            refine' ⟨I, hI, Xmap, φ, ⟨rfl, _⟩⟩ 
            suffices : Sigma.desc φ = 𝟙 _ 
            · rw [this]
              exact inferInstance 
            ext 
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
          intro Q q hq 
          simp only [Sieve.pullback_apply, Sieve.generate_apply] 
          simp only [Sieve.generate_apply] at hq    
          obtain ⟨E, e, r, hq⟩ := hq
          refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩  
          · rw [h]
            induction hq.1
            dsimp 
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
            exact Presieve.ofArrows.mk _
          · rw [← hq.2]
            rfl
    | top => 
      · apply Coverage.saturate.top
    | transitive Y T => 
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption   

lemma isSheafForDagurSieveSingle {X : ExtrDisc} {S : Presieve X} (hS : S ∈ DagurSieveSingle X)
    (F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)) : IsSheafFor F S := by
  obtain ⟨Y, f, rfl, hf⟩ := hS
  have proj : Projective (toCompHaus.obj X) := inferInstanceAs (Projective X.compHaus)
  have : Epi (toCompHaus.map f) := by
    rw [CompHaus.epi_iff_surjective]
    change Function.Surjective f
    rwa [← ExtrDisc.epi_iff_surjective]
  set g := toCompHaus.preimage <| Projective.factorThru (𝟙 _) (toCompHaus.map f) with hg
  have hfg : g ≫ f = 𝟙 _ := by
    refine' toCompHaus.map_injective _
    rw [map_comp, hg, image_preimage, Projective.factorThru_comp, CategoryTheory.Functor.map_id]
  intro y hy
  refine' ⟨F.map g.op <| y f <| ofArrows.mk (), fun Z h hZ => _, fun z hz => _⟩
  · cases' hZ with u
    have := hy (f₁ := f) (f₂ := f) (𝟙 Y) (f ≫ g) (ofArrows.mk ()) (ofArrows.mk ()) ?_
    · rw [op_id, F.map_id, types_id_apply] at this
      rw [← types_comp_apply (F.map g.op) (F.map f.op), ← F.map_comp, ← op_comp]
      exact this.symm
    · rw [Category.id_comp, Category.assoc, hfg, Category.comp_id]
  · have := congr_arg (F.map g.op) <| hz f (ofArrows.mk ())
    rwa [← types_comp_apply (F.map f.op) (F.map g.op), ← F.map_comp, ← op_comp, hfg, op_id,
      F.map_id, types_id_apply] at this

lemma isSheafFor_of_Dagur {X : ExtrDisc} {S : Presieve X}
  (hS : S ∈ (dagurCoverage ExtrDisc EverythinProj_ExtrDisc
    Extensivity_ExtrDisc).covering X)
  {F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)} (hF : PreservesFiniteProducts F) : S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForDagurSieveIso hSIso hF
  · exact isSheafForDagurSieveSingle hSSingle F

lemma final (A : Type (u+2)) [Category.{u+1} A] {F : ExtrDisc.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := by
  rw [← one']
  exact fun E => (Presieve.isSheaf_coverage _ _).2 <| fun S hS => isSheafFor_of_Dagur hS
    ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩
  exacts [ExtrDisc.EverythingProj_ExtrDisc, ExtrDisc.Extensivity_ExtrDisc]