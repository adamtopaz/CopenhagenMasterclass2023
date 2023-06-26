import ExtrDisc.Basic
import Mathlib.Topology.Constructions

open CategoryTheory TopologicalSpace

variable (A B: Type _) [TopologicalSpace A] [T2Space A] [CompactSpace A] [ExtremallyDisconnected A]
variable {C : Type _} [TopologicalSpace B] [TopologicalSpace C] [T2Space B] [T2Space C]
  [CompactSpace B] [CompactSpace C] 
variable {f : B → C} {φ : A → C} (hf : Continuous f) (hφ : Continuous φ) (hφ' : φ.Surjective)

def D : Set (A × B) := sorry

def π₁ : D A B → A := fun x ↦ x.val.fst

def π₂ : D A B → B := fun x ↦ x.val.snd

lemma one : CompactSpace (D A B) := sorry

lemma two : (π₁ A B).Surjective := sorry -- '' (Set.univ) = Set.univ := this does not work!

lemma three : ∃ (E : Set (D A B)), CompactSpace E ∧ (π₁ A B) '' E = Set.univ ∧ ∀ (E₀ : Set (D A B)),
 E₀ ⊆ E → CompactSpace E₀ → ¬ ((π₁ A B)'' E₀) = Set.univ := sorry

def E : (Set (D A B)) := (three A B).choose

def gleason23 (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r) :
  CompactSpace E → (∀ (E₀ : Set E), ¬ E₀ = ⊤ → CompactSpace E₀ → ¬ (r '' E₀ = ⊤)) → E ≃ₜ A := sorry

def ρ : (E A B) ≃ₜ A where
  toFun := (E A B).restrict (π₁ A B)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma five : Continuous ((E A B).restrict (π₂ A B) ∘ (ρ A B).invFun) ∧ 
  f ∘ ((E A B).restrict (π₂ A B) ∘ (ρ A B).invFun) = φ := sorry

-- #check five A B

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    sorry