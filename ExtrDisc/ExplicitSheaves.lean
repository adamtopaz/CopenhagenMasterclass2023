import ExtrDisc.Basic
import Sieves.dagur 


lemma one : (dagurCoverage ExtrDisc).toDCoverage = (coherentCoverage ExtrDisc).toDCoverage := 
  sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry

lemma final (A : Type _) [Category A] [Limits.HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : Limits.PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry