import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic

universe u

open CategoryTheory

structure ExtrDisc where
  compHaus : CompHaus.{u}
  [projective : Projective compHaus]

namespace ExtrDisc

instance : LargeCategory ExtrDisc.{u} :=  
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

instance : CoeSort ExtrDisc.{u} (Type u) where
  coe X := X.compHaus

example (X : ExtrDisc.{u}) : TopologicalSpace X := inferInstance
example (X : ExtrDisc.{u}) : CompactSpace X := inferInstance
example (X : ExtrDisc.{u}) : T2Space X := inferInstance

instance (X : ExtrDisc.{u}) : TotallyDisconnectedSpace X := sorry

@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := { toCompHaus := X.compHaus }
  map f := f

instance : Full toProfinite := sorry
instance : Faithful toProfinite := sorry

@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

instance : Full toCompHaus := sorry
instance : Faithful toCompHaus := sorry

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus := 
  rfl

instance (X : ExtrDisc) : Projective X.compHaus := X.projective

end ExtrDisc

namespace CompHaus

noncomputable
def presentation (X : CompHaus) : ExtrDisc where
  compHaus := (projectivePresentation X).p

noncomputable
def presentationπ  (X : CompHaus) : X.presentation.compHaus ⟶ X :=   
  (projectivePresentation X).f

noncomputable
instance epiPresentπ (X : CompHaus) : Epi X.presentationπ :=   
  (projectivePresentation X).epi

noncomputable
def lift {X Y : CompHaus} (f : X ⟶ Y) [Epi f] : Y.presentation.compHaus ⟶ X :=
  Projective.factorThru Y.presentationπ f 

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} (f : X ⟶ Y) [Epi f] :
    lift f ≫ f  = Y.presentationπ := by simp [lift]

end CompHaus