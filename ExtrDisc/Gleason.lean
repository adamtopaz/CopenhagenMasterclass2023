import ExtrDisc.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.Zorn

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

example (X Y : Set A) (h :X ⊂ Y) : (X⊆Y ) := by exact?

lemma three : ∃ (E : Set (D A B)), CompactSpace E ∧ (π₁ A B) '' E = Set.univ ∧ ∀ (E₀ : Set (D A B)),
 E₀ ⊂ E → CompactSpace E₀ → ¬ ((π₁ A B)'' E₀) = Set.univ := by
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



def E : (Set (D A B)) := (three A B).choose

def ρ : (E A B) ≃ₜ A := sorry

lemma five : Continuous ((E A B).restrict (π₂ A B) ∘ (ρ A B).invFun) ∧
  f ∘ ((E A B).restrict (π₂ A B) ∘ (ρ A B).invFun) = φ := sorry

-- #check five A B

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    sorry