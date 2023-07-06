import Sieves.ExtensiveRegular
import Profinite.Coherent
import Mathlib.CategoryTheory.Sites.Sheaf
import Profinite.Pullback
import Profinite.Coproduct

open CategoryTheory Profinite Opposite CategoryTheory.Limits Functor Presieve
 
namespace Profinite 

lemma extensivity_injective {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = σ ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (σ R₁) = f (σ R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective R₂ 
  have ha₁ : a₁ = R₁.fst := (congrArg Sigma.fst h₁).symm 
  have ha₂ : a₂ = R₂.fst := (congrArg Sigma.fst h₂).symm  
  have ha : a₁ = a₂ := by rwa [ha₁, ha₂] 
  have : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂) 
  · rw [← finiteCoproduct.range_eq ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply] 
  obtain ⟨xr', hr'⟩ := this 
  rw [← hr', h₂] at hR 
  have hf : ∀ (a : α), Function.Injective 
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · intro a 
    simp only [finiteCoproduct.ι_desc]  
    intro x y h 
    have h₁ := h
    apply_fun f at h 
    change (pullback.fst f (π a) ≫ f) x = _ at h 
    have h' := h.symm
    change (pullback.fst f (π a) ≫ f) y = _ at h'
    rw [pullback.condition] at h' 
    have : Function.Injective (π a)
    · intro r s hrs
      rw [← finiteCoproduct.ι_desc_apply] at hrs
      have hrs' := hrs.symm 
      rw [← finiteCoproduct.ι_desc_apply] at hrs' 
      have : Function.Injective (finiteCoproduct.desc (fun a ↦ Z a) π)
      · apply Function.Bijective.injective 
        exact ConcreteCategory.bijective_of_isIso _ 
      exact (finiteCoproduct.ι_injective a (this hrs')).symm
    have h₂ := this h' 
    suffices : x.val = y.val 
    · exact Subtype.ext this 
    exact Prod.ext h₁ h₂.symm
  have := hf a₂ hR 
  rw [← hr', h₂, this]

lemma extensivity_explicit {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  apply isIso_of_bijective _ 
  refine' ⟨extensivity_injective f HIso, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl  
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · apply Eq.symm
      change (_ ≫ inv β) _ = _
      rw [this]
      rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

lemma extensivity : Extensivity Profinite := @fun α _ X Z i Y f H => by
  let θ := Sigma.mapIso (fun a => fromExplicitIso f (i a))
  suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left θ.hom
  let δ := FromFiniteCoproductIso (fun a => Profinite.pullback f (i a))
  suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left δ.hom
  have HIso : IsIso (finiteCoproduct.desc _ i) := by
    let ε := ToFiniteCoproductIso Z
    suffices IsIso <| ε.hom ≫ (finiteCoproduct.desc _ i) by
      · apply IsIso.of_isIso_comp_left ε.hom 
    convert H
    refine' Sigma.hom_ext _ _ (fun a => _)
    simp [← Category.assoc]
  convert extensivity_explicit f HIso
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  simp [← Category.assoc, finiteCoproduct.ι_desc, fromExplicit]

lemma epi_pullback_of_epi : EpiPullbackOfEpi Profinite := by
  intro X Y Z f π hπ  
  suffices : Epi (fromExplicit f π ≫ (Limits.pullback.fst : Limits.pullback f π ⟶ Y))
  · exact @epi_of_epi _ _ _ _ _ _ _ this
  rw [Profinite.epi_iff_surjective] at hπ ⊢   
  intro y 
  obtain ⟨z,hz⟩ := hπ (f y) 
  have : fromExplicit f π ≫ Limits.pullback.fst = Profinite.pullback.fst f π
  · dsimp [fromExplicit]
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app] 
  rw [this] 
  exact ⟨⟨(y, z), hz.symm⟩, rfl⟩ 

lemma one' : (ExtensiveRegularCoverage' Profinite epi_pullback_of_epi 
    extensivity).toGrothendieck = 
    (coherentTopology Profinite) := by
  ext X S  
  constructor
  <;> intro h 
  · dsimp [Coverage.toGrothendieck] at *
    induction h with 
    | of Y T hT => 
      · apply Coverage.saturate.of 
        dsimp [coherentCoverage]
        dsimp [ExtensiveRegularCoverage'] at hT 
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
          rw [Profinite.epi_iff_surjective _] at h ⊢ 
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
          dsimp [ExtensiveRegularCoverage']
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
            (ExtensiveRegularCoverage' _ _ _).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (ExtensiveRegularCoverage' _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [ExtensiveRegularCoverage'] 
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

def MapToEqualizer (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {W X B : Profinite} (f : X ⟶ B) 
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) : 
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by 
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ ;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

def EqualizerCondition (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := ∀
  (X B : Profinite) (π : X ⟶ B) (_ : Function.Surjective π),
  Function.Bijective (MapToEqualizer P π (Profinite.pullback.fst π π) (Profinite.pullback.snd π π)
      (Profinite.pullback.condition _ _))
    
noncomputable
def EqualizerFirstObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B)
     : Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) := 
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫ 
  { hom := fun e ↦ e π (Presieve.singleton_self π)  
    inv := fun e _ _ h ↦ by 
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso_aux (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) := 
  Types.productIso.{u+1, u+1} _ ≪≫ 
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁ 
      induction h₂ 
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂ 
      rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Profinite.pullback π π)) := 
  EqualizerSecondObjIso_aux F π ≪≫ (F.mapIso ((fromExplicitIso π π).op : 
    op (Limits.pullback π π) ≅ op (Profinite.pullback π π)))

lemma isSheafFor_of_Dagur {B : Profinite} {S : Presieve B}
    (hS : S ∈ (ExtensiveRegularCoverage' Profinite epi_pullback_of_epi extensivity).covering B)
    {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (hFpfp : PreservesFiniteProducts F) 
    (hFecs : EqualizerCondition F) : 
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForExtensiveSieve hSIso hFpfp
  · rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    intro y h 
    dsimp [RegularSieve] at hSSingle 
    obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := hSSingle 
    rw [Presieve.ofArrows_pUnit] at hS 
    subst hS
    rw [Profinite.epi_iff_surjective] at πsurj 
    specialize hFecs X B π πsurj 
    have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom = 
        F.map π.op
    · dsimp [EqualizerFirstObjIso, Equalizer.forkMap]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have fmap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.fst π π).op = 
        Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      rw [Profinite.fst_comp_fromExplicit, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.fst.op = 
          Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom 
      · simp only [← Category.assoc] 
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.firstMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have smap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.snd π π).op = 
        Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom 
    · dsimp [EqualizerSecondObjIso]
      rw [Profinite.snd_comp_fromExplicit, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.snd.op = 
          Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom 
      · simp only [← Category.assoc] 
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.secondMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply] 
    have iy_mem : F.map (pullback.fst π π).op ((EqualizerFirstObjIso F π).hom y) = 
        F.map (pullback.snd π π).op ((EqualizerFirstObjIso F π).hom y)
    · change ((EqualizerFirstObjIso F π).hom ≫ _) y = _ 
      apply Eq.symm -- how do I avoid this ugly hack?
      change ((EqualizerFirstObjIso F π).hom ≫ _) y = _  
      rw [fmap_comp, smap_comp]
      dsimp 
      rw [h]
    have uniq_F : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
    · rw [Function.bijective_iff_existsUnique] at hFecs 
      specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, iy_mem⟩ 
      obtain ⟨x, hx⟩ := hFecs 
      refine' ⟨x, _⟩   
      dsimp [MapToEqualizer] at *
      refine' ⟨Subtype.ext_iff.mp hx.1,_⟩ 
      intro z hz 
      apply hx.2 
      rwa [Subtype.ext_iff] 
    obtain ⟨x,hx⟩ := uniq_F 
    dsimp at hx
    rw [← fork_comp] at hx
    use x   
    dsimp 
    constructor 
    · apply_fun (EqualizerFirstObjIso F π).hom 
      · exact hx.1 
      · apply Function.Bijective.injective 
        rw [← isIso_iff_bijective] 
        exact inferInstance
    · intro z hz
      apply_fun (EqualizerFirstObjIso F π).hom at hz
      exact hx.2 z hz
    
theorem final (A : Type (u+2)) [Category.{u+1} A] {F : Profinite.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F) 
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) : 
  Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [← one']
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _ 
  intro B S hS
  apply isSheafFor_of_Dagur hS 
  · exact ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩
  · exact hF' E 

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] 
    {F : Profinite.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts (F ⋙ G)) (hF' : EqualizerCondition (F ⋙ G)) : 
    Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Profinite) F G,
    isSheaf_iff_isSheaf_of_type, ← one', Presieve.isSheaf_coverage]
  intro B S' hS 
  exact isSheafFor_of_Dagur hS hF hF'

end Profinite