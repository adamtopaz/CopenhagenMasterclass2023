import ExtrDisc.Basic
import Sieves.dagur
import Mathlib.CategoryTheory.Sites.Sheaf
import ExtrDisc.Coherent


open CategoryTheory ExtrDisc

variable (C : Type _) [Category C] [Precoherent C]

def dagurCoverage [Limits.HasFiniteCoproducts C] : Coverage C where
  covering B := 
    { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Limits.Sigma.desc π) } ∪
    { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X) 
      (fun (_ : Unit) ↦ f) ∧ Epi f }
  pullback := by sorry


lemma one : (dagurCoverage ExtrDisc).toDCoverage = (coherentCoverage ExtrDisc).toDCoverage := 
  sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry

lemma dagur115_vi_to_sheaf (A : Type _) [Category A] [Limits.HasFiniteProducts C]
  {X : ExtrDisc} (F : ExtrDiscᵒᵖ ⥤ A) (S : Sieve X)
  (hS : ∀ (Y Z : ExtrDisc) (s : Y ⟶ X) (s' : Z ⟶ X), 
  S.arrows s → S.arrows s' → Limits.HasPullback s s') : true := sorry

lemma final (A : Type _) [Category A] [Limits.HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : Limits.PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry
