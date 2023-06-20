import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic

universe u

open CategoryTheory

structure ExtrDisc where
  compHaus : CompHaus.{u}
  projective : Projective compHaus

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

@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus := 
  rfl

end ExtrDisc