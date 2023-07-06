import Profinite.Epi

universe u

open CategoryTheory CategoryTheory.Limits

namespace Profinite

variable {α : Type} [Fintype α] (Z : α → Profinite.{u})

section FiniteCoproducts

section Iso

noncomputable
def toFiniteCoproduct : ∐ Z ⟶ finiteCoproduct Z :=
  Sigma.desc <| fun a => finiteCoproduct.ι Z a ≫ (𝟙 _)

noncomputable
def fromFiniteCoproduct : finiteCoproduct Z ⟶ ∐ Z :=
  finiteCoproduct.desc Z <| fun a => (Sigma.ι Z a)
  
@[simp]
theorem toFiniteCoproductCompFromFiniteCoproduct :
    (toFiniteCoproduct Z ≫ fromFiniteCoproduct Z) = 𝟙 _ := by
  ext
  simp [toFiniteCoproduct, fromFiniteCoproduct]

@[simp]
theorem FromFiniteCoproductComptToFiniteCoproduct :
    (fromFiniteCoproduct Z ≫ toFiniteCoproduct Z) = 𝟙 _ := by
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  simp [toFiniteCoproduct, fromFiniteCoproduct]

@[simps]
noncomputable
def FromFiniteCoproductIso : finiteCoproduct Z ≅ ∐ Z where
  hom := fromFiniteCoproduct Z
  inv := toFiniteCoproduct Z
  hom_inv_id := FromFiniteCoproductComptToFiniteCoproduct Z
  inv_hom_id := toFiniteCoproductCompFromFiniteCoproduct Z

@[simps]
noncomputable
def ToFiniteCoproductIso : ∐ Z ≅ finiteCoproduct Z where
  hom := toFiniteCoproduct Z
  inv := fromFiniteCoproduct Z
  hom_inv_id := toFiniteCoproductCompFromFiniteCoproduct Z
  inv_hom_id := FromFiniteCoproductComptToFiniteCoproduct Z

theorem IsIsotoFiniteCoproduct :
    IsIso (toFiniteCoproduct Z) :=
  ⟨fromFiniteCoproduct Z, by simp, by simp⟩

theorem IsIsofromFiniteCoproduct :
    IsIso (fromFiniteCoproduct Z) :=
  ⟨toFiniteCoproduct Z, by simp, by simp⟩

@[simp]
theorem Sigma.ιCompToFiniteCoproduct (a : α) :
    (Sigma.ι Z a) ≫ toFiniteCoproduct Z = finiteCoproduct.ι Z a := by
  simp [toFiniteCoproduct]
  
@[simp]
theorem finiteCoproduct.ιCompFromFiniteCoproduct (a : α) :
    (finiteCoproduct.ι Z a) ≫ fromFiniteCoproduct Z = Sigma.ι Z a := by
  simp [fromFiniteCoproduct]

@[simps] noncomputable
def toFiniteCoproductHomeo : (∐ Z : _) ≃ₜ finiteCoproduct Z where
  toFun := toFiniteCoproduct Z
  invFun := fromFiniteCoproduct Z
  left_inv := fun x => by
    change (toFiniteCoproduct Z ≫ fromFiniteCoproduct Z) x = x
    simp only [toFiniteCoproductCompFromFiniteCoproduct, id_apply]
  right_inv := fun x => by
    change (fromFiniteCoproduct Z ≫ toFiniteCoproduct Z) x = x
    simp only [FromFiniteCoproductComptToFiniteCoproduct, id_apply]
  continuous_toFun := (toFiniteCoproduct Z).continuous_toFun
  continuous_invFun := (fromFiniteCoproduct Z).continuous_toFun

theorem toFiniteCoproduct.OpenEmbedding : OpenEmbedding (toFiniteCoproductHomeo Z) :=
  Homeomorph.openEmbedding (toFiniteCoproductHomeo Z)

end Iso

lemma finiteCoproduct.ι_injective {α : Type} [Fintype α] {Z : α → Profinite.{u}} 
    (a : α) : Function.Injective (finiteCoproduct.ι Z a) := by
  intro x y hxy 
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective {α : Type} [Fintype α] {Z : α → Profinite.{u}} 
    (R : finiteCoproduct Z) : ∃ (a : α) (r : Z a), R = finiteCoproduct.ι Z a r := by
  exact ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} (a : α) : 
    ∀ x, finiteCoproduct.desc Z π (finiteCoproduct.ι Z a x) = π a x := by
  intro x 
  change (ι Z a ≫ desc Z π) _ = _ 
  simp only [ι_desc]

lemma finiteCoproduct.range_eq {α : Type} [Fintype α] {Z : α → Profinite.{u}} 
    {a b : α} (h : a = b) : Set.range (ι Z a) = Set.range (ι Z b) := by
  rw [h]

end FiniteCoproducts 

section Pullbacks

variable {X Y Z : Profinite.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (i : Y ⟶ Z) 

@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_,h⟩ ; exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {W : Profinite.{u}} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) :
    W ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w ; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {W : Profinite.{u}} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) :
  pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : Profinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
  pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : Profinite.{u}} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/--
The pullback cone whose cone point is the explicit pullback.
-/
@[simps! pt π]
def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

section Isos

noncomputable
def toExplicit : Limits.pullback f i ⟶ Profinite.pullback f i :=
  pullback.lift f i Limits.pullback.fst Limits.pullback.snd Limits.pullback.condition

noncomputable
def fromExplicit : Profinite.pullback f i ⟶ Limits.pullback f i :=
  Limits.pullback.lift (pullback.fst _ _) (pullback.snd _ _) (pullback.condition f i)

@[simp]
theorem toExplicitCompFromExcplict :
    (toExplicit f i ≫ fromExplicit f i) = 𝟙 _ := by
  refine' Limits.pullback.hom_ext (k := (toExplicit f i ≫ fromExplicit f i)) _ _
  · simp [toExplicit, fromExplicit]
  · rw [Category.id_comp, Category.assoc, fromExplicit, Limits.pullback.lift_snd,
      toExplicit, pullback.lift_snd]
    
@[simp]
theorem fromExcplictComptoExplicit :
    (fromExplicit f i ≫ toExplicit f i) = 𝟙 _ :=
  pullback.hom_ext f i _ _ (by simp [toExplicit, fromExplicit]) (by simp [toExplicit, fromExplicit])

@[simps]
noncomputable
def fromExplicitIso : Profinite.pullback f i ≅ Limits.pullback f i where
  hom := fromExplicit f i
  inv := toExplicit f i
  hom_inv_id := fromExcplictComptoExplicit f i
  inv_hom_id := toExplicitCompFromExcplict f i

end Isos

section Commutativity

theorem fst_comp_fromExplicit : 
    Profinite.pullback.fst f i = fromExplicit f i ≫ Limits.pullback.fst := by  
  dsimp [fromExplicit] 
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

theorem snd_comp_fromExplicit : 
    Profinite.pullback.snd f i = fromExplicit f i ≫ Limits.pullback.snd := by  
  dsimp [fromExplicit] 
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

end Commutativity

end Pullbacks 

end Profinite