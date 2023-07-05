import ExtrDisc.Basic
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sieves.ProdCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sieves.isSheafForPullbackSieve

universe u v w
section HasPullbackOfRightMono

open CategoryTheory Opposite CategoryTheory.Limits Functor

variable (C : Type u) [Category.{v, u} C] 

class HasPullbackOfIsIsodesc : Prop where
    HasPullback : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbackOfIsIsodesc C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C} 
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :  
    HasPullback f (i a) := HasPullbackOfIsIsodesc.HasPullback f i a

instance [HasPullbacks C] : HasPullbackOfIsIsodesc C := ⟨fun _ _ _ => inferInstance⟩

end HasPullbackOfRightMono

section Coverage
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] 

open Sieve CategoryTheory.Limits Opposite

variable {C}

def DagurSieveIso [HasFiniteCoproducts C] (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C)
  (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def DagurSieveSingle (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }

variable [HasFiniteCoproducts C] (C)

def Extensivity [HasPullbackOfIsIsodesc C] : Prop :=
  ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
  {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
     IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

def EverythingIsProjective : Prop :=
  ∀ X : C, Projective X

def dagurCoverage [HasFiniteCoproducts C] [HasPullbackOfIsIsodesc C]
    (h_proj : EverythingIsProjective C) (h_ext : Extensivity C) : Coverage C where
  covering B :=   (DagurSieveIso B) ∪ (DagurSieveSingle B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [DagurSieveIso] 
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
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
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        cases hg
        simp only [Category.id_comp]
        use Z
        use @Projective.factorThru C _ Y X Z ?_ f π h_epi
        exact h_proj Y
        use π
        constructor
        · cases hπ
          rw [Presieve.ofArrows_pUnit]
          exact Presieve.singleton.mk
        · have : Projective Y
          exact h_proj Y
          exact @Projective.factorThru_comp C _ Y X Z this f π h_epi

def EpiPullbackOfEpi [HasPullbacks C] : Prop := ∀ {X Y Z : C} (f : Y ⟶ X) (π : Z ⟶ X) [Epi π], 
    Epi (@pullback.fst _ _ _ _ _ f π _)

def dagurCoverage' [HasFiniteCoproducts C] [HasPullbacks C] (h_epi_epi : EpiPullbackOfEpi C) 
    (h_ext : Extensivity C) : Coverage C where
  covering B := (DagurSieveIso B) ∪ (DagurSieveSingle B) 
  pullback := by 
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [DagurSieveIso]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (@pullback.fst _ _ _ _ _ f π _) with hS'
      use S'
      constructor
      · right 
        rw [DagurSieveSingle]
        refine' ⟨(pullback f π), _, by {rw [Presieve.ofArrows_pUnit _]}, h_epi_epi f π⟩
      · rw [hS', Presieve.FactorsThruAlong]
        rintro _ _ ⟨⟩ 
        refine' ⟨Z, pullback.snd, π, ⟨_, by rw [pullback.condition]⟩⟩
        rw [hπ] 
        exact Presieve.ofArrows.mk ()

variable [HasPullbackOfIsIsodesc C] {C}

lemma isPullbackSieve_DagurSieveIso {X : C} {S : Presieve X}
    (hS : S ∈ DagurSieveIso X) : isPullbackPresieve S := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩ 
  intro Y₁ Y₂ f hf g hg
  rw [hS] at hf hg
  cases' hg with b
  apply HasPullbackOfIsIsodesc.HasPullback f

lemma DagurSieveIsoFinite {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X) :
    Finite (ΣY, { f : Y ⟶ X // S f }) := by
  rcases hS with ⟨α, _, Z, π, hS, _⟩
  classical
  refine' Fintype.finite (Fintype.ofSurjective (fun a => ⟨Z a, π a, hS ▸ Presieve.ofArrows.mk a⟩)
    (fun ⟨Y, ⟨f, hf⟩⟩ => _))
  cases' (hS ▸ hf) with a h
  exact ⟨a, rfl⟩

def v {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : α → Σ(Y : C), { f : Y ⟶ X // S f } :=
  fun a => ⟨Z a, π a, hS ▸ Presieve.ofArrows.mk a⟩

lemma vsurj {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : Function.Surjective (v hS) := fun ⟨Y, ⟨f, hf⟩⟩ => by
  cases' (hS ▸ hf) with a h
  exact ⟨a, rfl⟩

lemma v.fst {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).1 = Z a := rfl

lemma v.snd {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).2.1 = π a := rfl

noncomputable
def w {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : (Σ(Y : C), { f : Y ⟶ X // S f }) → α :=
  Classical.choose (vsurj hS).hasRightInverse

lemma vw {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : Function.RightInverse (w hS) (v hS) :=
  Classical.choose_spec _

lemma Zf {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (f : (Y : C) × { f // S f }) : Z (w hS f) = f.fst := by
    nth_rewrite 2 [← (vw hS) f]
    exact v.fst hS (w hS f)

noncomputable
def IsotoZ {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (f : (Σ(Y : C), { f : Y ⟶ X // S f })) :
  op (f.1) ≅ op (Z ((w hS) f)) := Iso.op <| eqToIso (Zf hS f)


noncomputable
def FintypeT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : Fintype (Σ(Y : C), { f : Y ⟶ X // S f }) := by
  classical
  exact Fintype.ofSurjective _ (vsurj hS)

lemma HasProductT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : HasProduct
     fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => (op f.1) := by
  suffices Finite (Σ(Y : C), { f : Y ⟶ X // S f }) by
    · infer_instance
  exact Fintype.finite <| FintypeT hS

noncomputable
def E {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) :
     haveI := FintypeT hS
     (Σ(Y : C), { f : Y ⟶ X // S f }) ≃
     Fin (Fintype.card (Σ(Y : C), { f : Y ⟶ X // S f })) :=  
  @Fintype.equivFin _ (_)

noncomputable
def comparison {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (F : Cᵒᵖ ⥤ Type max u v) :
    haveI := HasProductT hS
    (∏ fun a => F.obj (op (Z a))) ⟶ 
    ∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => F.obj (op f.1) :=
  haveI := HasProductT hS
  Pi.lift (fun f => Pi.π _ _ ≫ F.map (IsotoZ hS f).inv)

noncomputable
def comparisoninv {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (F : Cᵒᵖ ⥤ Type max u v) :
    haveI := HasProductT hS
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => F.obj (op f.1)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  haveI := HasProductT hS
  Pi.lift (fun a => Pi.π _ (v hS a) ≫ F.map (𝟙 _)) 
  
noncomputable
def fromFirst {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) {F : Cᵒᵖ ⥤ Type max u v} (hF : PreservesFiniteProducts F)
    (HIso : IsIso (Sigma.desc π)) :
    Equalizer.FirstObj F S ⟶ F.obj (op X) :=
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
    haveI := (hF.preserves α); infer_instance
  comparisoninv hS F ≫ ((Limits.PreservesProduct.iso F (fun a => op <| Z a)).inv ≫
    F.map (CoprodToProd Z).inv ≫ F.map (inv (Sigma.desc π).op))

lemma piCompInvdesc {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    (HIso : IsIso (Sigma.desc π)) (a : α) : π a ≫ inv (Sigma.desc π) = Sigma.ι _ a := by
  simp

lemma PreservesProduct.isoInvCompMap {C : Type u} [Category C] {D : Type v} [Category D] (F : C ⥤ D)
    {J : Type w} {f : J → C} [HasProduct f] [HasProduct (fun j => F.obj (f j))]
    [PreservesLimit (Discrete.functor f) F] (j : J) :
    (PreservesProduct.iso F f).inv ≫ F.map (Pi.π _ j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (⟨j⟩ : Discrete J)

lemma isSheafForDagurSieveIsIsoFork {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    IsIso (Equalizer.forkMap F S) := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
      haveI := (hF.preserves α); infer_instance
  refine' ⟨fromFirst hS hF HIso, _, _⟩
  · unfold fromFirst 
    simp only [← Category.assoc]
    rw [Functor.map_inv, IsIso.comp_inv_eq, Category.id_comp, ← Functor.mapIso_inv,
      Iso.comp_inv_eq, Functor.mapIso_hom, Iso.comp_inv_eq, ← Functor.map_comp, descOpCompCoprodToProd]
    have : F.map (Pi.lift fun a => (π a).op) ≫ (PreservesProduct.iso F fun a => op (Z a)).hom =
      Pi.lift (fun a => F.map ((Sigma.ι Z a ≫ (Sigma.desc π)).op)) := by simp --this can be a general lemma
    erw [this]
    refine' funext (fun s => _)
    simp only [types_comp_apply, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    ext a
    rw [Types.Limit.lift_π_apply]
    dsimp [comparisoninv]
    simp_rw [v.fst]
    simp only [Functor.map_id, Category.comp_id]
    rw [Types.Limit.lift_π_apply]
    simp only [Fan.mk_pt, Equalizer.forkMap, Fan.mk_π_app, Types.pi_lift_π_apply, v.snd]
  · refine' Limits.Pi.hom_ext _ _ (fun f => _)
    dsimp [Equalizer.forkMap]
    rw [Category.id_comp, Category.assoc, limit.lift_π, Limits.Fan.mk_π_app]
    simp only
    obtain ⟨a, ha⟩ := vsurj hS f
    unfold fromFirst
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← op_inv, ← op_comp, ← ha, v.snd hS, piCompInvdesc,
      ← Functor.map_comp, CoprodToProdInvComp.ι, @PreservesProduct.isoInvCompMap _ _ _ _ F _ _ _ _ (_) a]
    simp only [comparisoninv, op_id, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    erw [F.map_id, Category.comp_id]    

lemma isSheafForDagurSieveIso {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    Presieve.IsSheafFor F S := by    
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_DagurSieveIso hS).2 _
  rw [Limits.Types.type_equalizer_iff_unique]
  dsimp [Equalizer.FirstObj]
  suffices IsIso (Equalizer.forkMap F S) by
    · intro y _
      refine' ⟨inv (Equalizer.forkMap F S) y, _, fun y₁ hy₁ => _⟩
      · change (inv (Equalizer.forkMap F S) ≫ (Equalizer.forkMap F S)) y = y 
        rw [IsIso.inv_hom_id, types_id_apply]
      · replace hy₁ := congr_arg (inv (Equalizer.forkMap F S)) hy₁
        change ((Equalizer.forkMap F S) ≫ inv (Equalizer.forkMap F S)) _ = _ at hy₁
        rwa [IsIso.hom_inv_id, types_id_apply] at hy₁
  exact isSheafForDagurSieveIsIsoFork hS hF

end CategoryTheory

end Coverage