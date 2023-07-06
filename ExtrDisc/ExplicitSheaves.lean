import ExtrDisc.Basic
import ExtrDisc.Coherent
import Mathlib.CategoryTheory.Sites.Sheaf
import Sieves.isSheafForPullbackSieve
import Sieves.ExtensiveRegular
import Sieves.OpenEmbedding
import ExtrDisc.Pullback

universe u v

open CategoryTheory ExtrDisc Opposite CategoryTheory.Limits Functor Presieve

namespace CategoryTheory

open CategoryTheory.Limits

namespace ExtrDisc

lemma OpenEmbedding_of_Sigma_desc_Iso {α : Type} [Fintype α] {X : ExtrDisc.{u}}
    {Z : α → ExtrDisc.{u}} {i : (a : α) → Z a ⟶ X} (HIso : IsIso (Sigma.desc i)) :
    ∀ a, OpenEmbedding (i a) := by
  intro a
  have h₁ : OpenEmbedding (Sigma.desc i) :=
    (ExtrDisc.homeoOfIso (asIso (Sigma.desc i))).openEmbedding
  have h₂ : OpenEmbedding (Sigma.ι Z a) := openEmbedding_ι _ _
  have := OpenEmbedding.comp h₁ h₂
  erw [← CategoryTheory.coe_comp (Sigma.ι Z a) (Sigma.desc i)] at this 
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at this 
  assumption

instance : HasPullbackOfIsIsodesc ExtrDisc := by
  constructor 
  intro X Z α f Y i _ _ _ a 
  apply HasPullbackOpenEmbedding 
  apply OpenEmbedding_of_Sigma_desc_Iso inferInstance

lemma isIso_of_bijective {X Y : ExtrDisc.{u}} {f : X ⟶ Y} (hf : Function.Bijective f) : IsIso f := by
  suffices IsIso <| toCompHaus.map f by
    · apply isIso_of_fully_faithful toCompHaus
  exact CompHaus.isIso_of_bijective _ hf

lemma Extensivity_ExtrDisc_injective {α : Type} [Fintype α] {X : ExtrDisc.{u}}
    {Z : α → ExtrDisc.{u}} {π : (a : α) → Z a ⟶ X} {Y : ExtrDisc.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) (hOpen : ∀ a, OpenEmbedding (π a)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (hOpen a) ≫ finiteCoproduct.ι Z a )
  let α := finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = α ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (α R₁) = f (α R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  exact Sigma.subtype_ext Hfst hR 

lemma Extensivity_ExtrDisc_explicit {α : Type} [Fintype α] {X : ExtrDisc.{u}}
    {Z : α → ExtrDisc.{u}} {π : (a : α) → Z a ⟶ X} {Y : ExtrDisc.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) (hOpen : ∀ a, OpenEmbedding (π a)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let β := finiteCoproduct.desc _ π
  refine' isIso_of_bijective ⟨Extensivity_ExtrDisc_injective f HIso hOpen, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨y, (inv β (f y)).2, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl  
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · change (_ ≫ inv β) _ = _
      rw [this]
      rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

lemma Extensivity_ExtrDisc : Extensivity ExtrDisc := @fun α _ X Z i Y f H => by
  have hOpen := OpenEmbedding_of_Sigma_desc_Iso H
  let θ := Sigma.mapIso (fun a => fromExplicitIso f (hOpen a))
  suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left θ.hom
  let δ := FromFiniteCoproductIso (fun a => (OpenEmbeddingCone f (hOpen a)).pt)
  suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left δ.hom
  have HIso : IsIso (finiteCoproduct.desc _ i) := by
    let ε := ToFiniteCoproductIso Z
    suffices IsIso <| ε.hom ≫ (finiteCoproduct.desc _ i) by
      · apply IsIso.of_isIso_comp_left ε.hom 
    convert H
    refine' Sigma.hom_ext _ _ (fun a => _)
    simp [← Category.assoc]
  convert Extensivity_ExtrDisc_explicit f HIso hOpen
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  simp [← Category.assoc, finiteCoproduct.ι_desc, fromExplicit]

lemma EverythingProj_ExtrDisc : EverythingIsProjective ExtrDisc := by
  refine' fun P => ⟨(@fun X Y f e he => _)⟩
  have proj : Projective (toCompHaus.obj P) := inferInstanceAs (Projective P.compHaus)
  have : Epi (toCompHaus.map e) := by --TODO state a general lemma
    rw [CompHaus.epi_iff_surjective]
    change Function.Surjective e
    rwa [← ExtrDisc.epi_iff_surjective]
  set g := toCompHaus.preimage <| Projective.factorThru (toCompHaus.map f) (toCompHaus.map e) with hg
  refine' ⟨g, toCompHaus.map_injective _⟩
  rw [map_comp, hg, image_preimage, Projective.factorThru_comp]

end ExtrDisc

end CategoryTheory

lemma one' : (ExtensiveRegularCoverage ExtrDisc EverythingProj_ExtrDisc
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
        dsimp [ExtensiveRegularCoverage] at hT 
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
          dsimp [ExtensiveRegularCoverage]
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
            (ExtensiveRegularCoverage _ _ _).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (ExtensiveRegularCoverage _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [ExtensiveRegularCoverage] 
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

lemma isSheafForRegularSieve {X : ExtrDisc} {S : Presieve X} (hS : S ∈ RegularSieve X)
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

lemma isSheafFor_of_extensiveRegular {X : ExtrDisc} {S : Presieve X}
  (hS : S ∈ (ExtensiveRegularCoverage ExtrDisc EverythinProj_ExtrDisc
    Extensivity_ExtrDisc).covering X)
  {F : ExtrDisc.{u}ᵒᵖ ⥤ Type (u+1)} (hF : PreservesFiniteProducts F) : S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForExtensiveSieve hSIso hF
  · exact isSheafForRegularSieve hSSingle F

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : ExtrDisc.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := by
  rw [← one']
  exact fun E => (Presieve.isSheaf_coverage _ _).2 <| fun S hS => isSheafFor_of_extensiveRegular hS
    ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩