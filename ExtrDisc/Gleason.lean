import ExtrDisc.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.Zorn

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

lemma three : ∃ (E : Set (D A B)), CompactSpace E ∧ (π₁ A B) '' E = Set.univ ∧ ∀ (E₀ : Set (D A B)),
 E₀ ⊆ E → CompactSpace E₀ → ¬ ((π₁ A B)'' E₀) = Set.univ := by
 -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set (D A B) | CompactSpace E ∧ (π₁ A B) '' E = Set.univ}
  have : (∀ (c : Set (Set ↑(D A B))),
    c ⊆ S → IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D A B)), s ∈ c → lb ⊆ s) := by sorry
  have := zorn_superset S this
  rcases this with ⟨E, ⟨⟨hE₁,hE₂⟩, hE₃⟩⟩
  use E
  constructor
  · exact hE₁
  constructor
  · exact hE₂
  --Now, it's just rephrasing the conclusion of Zorn's Lemma
  · intro E₀ h₁ h₂
    replace hE₃ := hE₃ E₀
    by_contra h₃
    replace hE₃ := hE₃ (And.intro h₂ h₃) (subset_of_ssubset h₁)
    exact (ne_of_ssubset h₁) hE₃


def E : (Set (D φ f)) := (three).choose

def gleason23 (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r) :
  CompactSpace E → (∀ (E₀ : Set E), ¬ E₀ = ⊤ → CompactSpace E₀ → ¬ (r '' E₀ = ⊤)) → E ≃ₜ A := sorry

def ρ : (E A B) ≃ₜ A where
  toFun := (E A B).restrict (π₁ A B)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma five : Continuous (E.restrict (π₂ φ f) ∘ ρ.invFun) ∧
  f ∘ ((E φ f).restrict (π₂ φ f) ∘ ρ.invFun) = φ := sorry

-- #check five A B

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    sorry