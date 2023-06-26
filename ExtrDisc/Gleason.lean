import ExtrDisc.Basic

open CategoryTheory

lemma gleason (X : ExtrDisc) : Projective X.compHaus := sorry

variable (A : Type _) [TopologicalSpace A] [T2Space A] [CompactSpace A] [ExtremallyDisconnected A]
variable [TopologicalSpace B] [TopologicalSpace C] [T2Space B] [T2Space C] [CompactSpace B]
  [CompactSpace C] 
variable {f : B → C} {φ : A → C} (hf : Continuous f) (hφ : Continuous φ) (hφ' : φ.Surjective)

variable (B)
def D : Set (A × B) := sorry

def π₁ : D A B → A := fun x ↦ x.val.fst

def π₂ : D A B → B := fun x ↦ x.val.snd

variable {B}

example : TopologicalSpace (D A B) := inferInstance

lemma one : CompactSpace (D A B) := sorry