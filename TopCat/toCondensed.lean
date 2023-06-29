import Mathlib.Condensed.Abelian

#check Condensed

open CategoryTheory

universe u

def TopCat.ulift' : TopCat.{u} ⥤ TopCat.{u+1} where
  obj X := of (ULift.{u+1} X) 
  map f := sorry
  map_id := sorry
  map_comp := sorry



def TopCat.toCondensed : TopCat.{u+1} ⥤ Condensed.{u} (Type (u+1)) where
  obj X := {
    val := (compHausToTop : CompHaus ⥤ TopCat.{u}).op ⋙ 
      (sorry : TopCat.{u} ⥤ TopCat.{u+1}).op ⋙ 
      (yoneda.obj X : TopCat.{u+1}ᵒᵖ ⥤ Type (u+1))
    cond := sorry -- sheaf condition
  }
  map := sorry -- data
  map_id := sorry -- proof
  map_comp := sorry -- proof

#check whiskerRight

theorem CompHausCondIsSheaf : 
    Presheaf.IsSheaf (coherentTopology CompHaus) (yoneda.obj X ⋙ uliftFunctor) := by
  -- now Adam takes over
  sorry

def CompHaus.toCondensed : CompHaus.{u} ⥤ Condensed.{u} (Type (u+1)) where
  obj X := {
    val := yoneda.obj X ⋙ (uliftFunctor.{u+1} : Type u ⥤ Type (u+1))
    cond := CompHausCondIsSheaf -- sheaf condition
  }
  map f := ⟨whiskerRight (yoneda.map f) _⟩