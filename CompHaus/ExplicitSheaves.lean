import Sieves.dagur
import CompHaus.Pullback
import CompHaus.Coproduct
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
import Mathlib.CategoryTheory.Sites.Sheaf

open CategoryTheory CompHaus Opposite CategoryTheory.Limits Functor Presieve
 
namespace CompHaus

lemma finiteCoproduct.ι_injective {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    (a : α) : Function.Injective (finiteCoproduct.ι Z a) := by
  intro x y hxy 
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    (R : finiteCoproduct Z) : ∃ (a : α) (r : Z a), R = finiteCoproduct.ι Z a r := by
  exact ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} (a : α) : 
    ∀ x, finiteCoproduct.desc Z π (finiteCoproduct.ι Z a x) = π a x := by
  intro x 
  change (ι Z a ≫ desc Z π) _ = _ 
  simp only [ι_desc]

lemma finiteCoproduct.range_eq {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    {a b : α} (h : a = b) : Set.range (ι Z a) = Set.range (ι Z b) := by
  rw [h]

lemma extensivity_injective {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
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

lemma extensivity_explicit {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
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

lemma extensivity : Extensivity CompHaus := @fun α _ X Z i Y f H => by
  let θ := Sigma.mapIso (fun a => fromExplicitIso f (i a))
  suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left θ.hom
  let δ := FromFiniteCoproductIso (fun a => CompHaus.pullback f (i a))
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

lemma epi_pullback_of_epi : EpiPullbackOfEpi CompHaus := by
  intro X Y Z f π hπ  
  suffices : Epi (fromExplicit f π ≫ (Limits.pullback.fst : Limits.pullback f π ⟶ Y))
  · exact @epi_of_epi _ _ _ _ _ _ _ this
  rw [CompHaus.epi_iff_surjective] at hπ ⊢   
  intro y 
  obtain ⟨z,hz⟩ := hπ (f y) 
  have : fromExplicit f π ≫ Limits.pullback.fst = CompHaus.pullback.fst f π
  · dsimp [fromExplicit]
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app] 
  rw [this] 
  exact ⟨⟨(y, z), hz.symm⟩, rfl⟩ 

lemma one' : (dagurCoverage' CompHaus epi_pullback_of_epi 
    extensivity).toGrothendieck = 
    (coherentTopology CompHaus) := by
  ext X S  
  constructor
  <;> intro h 
  · dsimp [Coverage.toGrothendieck] at *
    induction h with 
    | of Y T hT => 
      · apply Coverage.saturate.of 
        dsimp [coherentCoverage]
        dsimp [dagurCoverage'] at hT 
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
          rw [CompHaus.epi_iff_surjective _] at h ⊢ 
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
          dsimp [dagurCoverage']
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
            (dagurCoverage' _ _ _).toGrothendieck R 
          · exact this 
          apply GrothendieckTopology.pullback_stable' 
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (dagurCoverage' _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of 
            dsimp [dagurCoverage'] 
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

lemma isSheafFor_of_Dagur {X : CompHaus} {S : Presieve X}
    (hS : S ∈ (dagurCoverage' CompHaus epi_pullback_of_epi extensivity).covering X)
    {F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)} (hFpfp : PreservesFiniteProducts F) 
    (hFecs : ∀ {S : Presieve X} (_ : S ∈ DagurSieveSingle X), IsSheafFor F S) : 
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForDagurSieveIso hSIso hFpfp
  · exact hFecs hSSingle 

end CompHaus