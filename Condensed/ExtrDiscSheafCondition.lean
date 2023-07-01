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

lemma isSheafOfIsColimit 
    (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) 
    (S : Cocone (F ⋙ sheafToPresheaf _ _))
    (hS : IsColimit S) : 
    Presheaf.IsSheaf (coherentTopology _) S.pt := by 
  have : HasColimit (F ⋙ sheafToPresheaf _ _) := ⟨S,hS⟩ 
  let e : S.pt ≅ colimit (F ⋙ sheafToPresheaf _ _) := 
    hS.coconePointUniqueUpToIso (colimit.isColimit _)
  rw [Presheaf.isSheaf_of_iso_iff e]
  apply isSheafColimit

def isColimitMap
    (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) 
    (S : Cocone F)
    (hS : IsColimit (sheafToPresheaf _ _ |>.mapCocone S)) :
    IsColimit S where
  desc E := .mk <| hS.desc <| sheafToPresheaf _ _ |>.mapCocone E
  fac _ _ := Sheaf.Hom.ext _ _ <| hS.fac _ _
  uniq E _ hm := Sheaf.Hom.ext _ _ <| hS.uniq 
    (s := sheafToPresheaf _ _ |>.mapCocone E) _ 
    fun j => congr_arg Sheaf.Hom.val <| hm j

instance (F : J ⥤ Sheaf (coherentTopology ExtrDisc.{u}) A) :
    CreatesColimit F (sheafToPresheaf (coherentTopology ExtrDisc.{u}) A) where
  reflects hS := isColimitMap _ _ <| hS
  lifts S hS := {
    liftedCocone := {
      pt := ⟨S.pt, isSheafOfIsColimit _ _ hS⟩ 
      ι := {
        app := fun _ => .mk <| S.ι.app _
        naturality := fun _ _ _ => Sheaf.Hom.ext _ _ <| S.ι.naturality _ } }
    validLift := Iso.refl _ }

instance : CreatesColimits
    (sheafToPresheaf (coherentTopology ExtrDisc.{u}) A) := by
  constructor ; unfold autoParam ; intro J _ 
  constructor ; unfold autoParam ; intro K
  infer_instance

end Sheaf

end ExtrDisc