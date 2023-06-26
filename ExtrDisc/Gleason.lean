import ExtrDisc.Basic
import Mathlib.Topology.Constructions

open CategoryTheory TopologicalSpace

variable {A : Type _} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ExtremallyDisconnected A]
variable {B C : Type _} [TopologicalSpace B] [TopologicalSpace C] [T2Space B] [T2Space C]
  [CompactSpace B] [CompactSpace C] 
variable (φ : A → C) (f : B → C)

def D : Set (A × B) := {x | φ x.fst = f x.snd}

def π₁ : D φ f → A := fun x ↦ x.val.fst

def π₂ : D φ f → B := fun x ↦ x.val.snd

variable {φ} {f} (hφ : Continuous φ) (hφ' : φ.Surjective) (hf : Continuous f) 

lemma one : CompactSpace (D φ f) := sorry

lemma two : (π₁ φ f).Surjective := sorry -- '' (Set.univ) = Set.univ := this does not work!

lemma three : ∃ (E : Set (D φ f)), CompactSpace E ∧ (π₁ φ f) '' E = Set.univ ∧ ∀ (E₀ : Set (D φ f)),
 E₀ ⊆ E → CompactSpace E₀ → ¬ ((π₁ φ f)'' E₀) = Set.univ := sorry

def E : (Set (D φ f)) := (three).choose

def ρ : E ≃ₜ A := sorry

lemma five : Continuous (E.restrict (π₂ φ f) ∘ ρ.invFun) ∧ 
  f ∘ ((E φ f).restrict (π₂ φ f) ∘ ρ.invFun) = φ := sorry

-- #check five A B

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    sorry