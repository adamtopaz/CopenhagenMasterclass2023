import ExtrDisc.Basic
import Sieves.dagur 


lemma one : (dagurCoverage ExtrDisc).toDCoverage = (coherentCoverage ExtrDisc).toDCoverage := 
  sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry

lemma dagur115_vi_to_sheaf (A : Type _) [Category A] [Limits.HasFiniteProducts C]
  {X : ExtrDisc} (F : ExtrDiscᵒᵖ ⥤ A) (S : Sieve ExtrDisc) (Y : ExtrDisc)
  (hS : ∀ s s' : S.arrows, Limits.HasPullback s s') : true := sorry

lemma final (A : Type _) [Category A] [Limits.HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : Limits.PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry
