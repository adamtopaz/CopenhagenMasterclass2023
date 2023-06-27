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

lemma dagur115_vi_to_sheaf {X : ExtrDisc} (F : ExtrDiscᵒᵖ ⥤ Type _) (S : Presieve X)
    (hS : ∀ {Y : ExtrDisc} (s : Y ⟶ X) {Z : ExtrDisc} (s' : Z ⟶ X), 
    S s → S s' → Limits.HasPullback s s') : sorry ↔ S.IsSheafFor F := sorry

lemma final (A : Type _) [Category A] [Limits.HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ A)
  (hf : Limits.PreservesFiniteProducts F) : Presheaf.IsSheaf (coherentTopology ExtrDisc) F := sorry
