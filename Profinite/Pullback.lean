import Profinite.Epi

open CategoryTheory Limits

namespace Profinite

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

end Profinite