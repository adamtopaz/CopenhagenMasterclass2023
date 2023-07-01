import ExtrDisc.Coherent
import Condensed.Equivalence

namespace ExtrDisc

open CategoryTheory Limits

universe u

theorem sheafCondition {A : Type (u+2)} [Category.{u+1} A] (F : ExtrDisc.{u}ᵒᵖ ⥤ A) :
  Nonempty (PreservesFiniteProducts F) ↔ 
  Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry

namespace Sheaf

variable {A : Type (u+2)} [Category.{u+1} A] 
variable [HasZeroMorphisms A] [HasFiniteBiproducts A]
variable {J : Type (u+1)} [SmallCategory J]

variable (F : J ⥤ ExtrDisc.{u}ᵒᵖ ⥤ A)

theorem isSheafColimitAux [HasColimit F] 
  (h : ∀ j : J, Presheaf.IsSheaf (coherentTopology ExtrDisc.{u}) (F.obj j)) : 
  Presheaf.IsSheaf (coherentTopology ExtrDisc.{u}) (colimit F) := sorry

theorem isSheafColimit (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) 
    [HasColimit (F ⋙ sheafToPresheaf _ _)] : 
    Presheaf.IsSheaf (coherentTopology ExtrDisc.{u}) 
    (colimit (F ⋙ sheafToPresheaf _ _)) := by
  apply isSheafColimitAux
  intro j
  apply Sheaf.cond

@[simps]
noncomputable
def colimitCocone 
    (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) 
    [HasColimit (F ⋙ sheafToPresheaf _ _)] :
    Cocone F where
  pt := {
    val := colimit (F ⋙ sheafToPresheaf _ _)
    cond := isSheafColimit _ }
  ι := {
    app := fun j => .mk <| colimit.ι (F ⋙ sheafToPresheaf _ _) j
    naturality := fun i j f => Sheaf.Hom.ext _ _ <| 
      by simpa using colimit.w (F ⋙ sheafToPresheaf _ _) _ }

noncomputable
def isColimitColimitCocone
    (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) 
    [HasColimit (F ⋙ sheafToPresheaf _ _)] :
    IsColimit (colimitCocone F) where
  desc := fun S => .mk <| 
    colimit.desc (F := F ⋙ sheafToPresheaf _ _) ((sheafToPresheaf _ _).mapCocone S)
  uniq S m hm := by
    ext1 
    apply colimit.hom_ext
    intro j
    simpa using congr_arg Sheaf.Hom.val (hm j)

end Sheaf

end ExtrDisc