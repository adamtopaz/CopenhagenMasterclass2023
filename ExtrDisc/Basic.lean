import Mathlib.Topology.Category.CompHaus.Projective

universe u

open CategoryTheory

structure ExtrDisc where
  compHaus : CompHaus.{u}
  projective : Projective compHaus

namespace ExtrDisc

instance : LargeCategory ExtrDisc.{u} :=  
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

end ExtrDisc