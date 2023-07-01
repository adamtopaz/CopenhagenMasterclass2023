import ExtrDisc.Coherent
import Condensed.Equivalence

namespace ExtrDisc

open CategoryTheory Limits

universe u

theorem sheafCondition (A : Type (u+2)) [Category.{u+1} A] (F : ExtrDisc.{u}ᵒᵖ ⥤ A) :
  Nonempty (PreservesFiniteProducts F) ↔ 
  Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry

end ExtrDisc