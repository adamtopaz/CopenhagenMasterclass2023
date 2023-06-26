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

variable {φ} {f} (hφ : Continuous φ) (hf : Continuous f) (hf' : f.Surjective)

lemma one : CompactSpace (D φ f) :=
isCompact_iff_compactSpace.mp (IsClosed.isCompact
  (isClosed_eq (Continuous.comp hφ continuous_fst) (Continuous.comp hf continuous_snd )))

lemma two : (π₁ φ f).Surjective := by
  intro a
  obtain ⟨b, hb⟩ := hf' (φ a)
  use ⟨(a,b), hb.symm⟩
  rfl

lemma three : ∃ (E : Set (D φ f)), CompactSpace E ∧ (π₁ φ f) '' E = Set.univ ∧ ∀ (E₀ : Set (D φ f)),
 E₀ ⊂ E → CompactSpace E₀ → ¬ ((π₁ φ f)'' E₀) = Set.univ := by
 -- Define the set of closed subsets of D for which the map onto A is surjective
  let S := { E : Set (D φ f) | CompactSpace E ∧ (π₁ φ f) '' E = Set.univ}
  have : (∀ (c : Set (Set ↑(D φ f))),
    c ⊆ S → IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D φ f)), s ∈ c → lb ⊆ s) := by sorry
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

def ρ : @E _ _ _ _ _ φ f ≃ₜ A where
  toFun := (@E _ _ _ _ _ φ f).restrict (π₁ φ f)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma five : Continuous (E.restrict (π₂ φ f) ∘ ρ.invFun) ∧ f ∘ (E.restrict (π₂ φ f) ∘ ρ.invFun) = φ := by
  constructor
  · exact Continuous.comp (ContinuousOn.restrict <| Continuous.continuousOn <|
      Continuous.snd continuous_subtype_val) ρ.continuous_invFun
  · ext a
    convert_to φ (E.restrict (π₁ φ f) <| ρ.invFun a) = φ a
    · simp only [π₁, π₂, Function.comp_apply, Set.restrict_apply]
      rcases ρ.invFun a with ⟨⟨_, ha⟩, _⟩
      exact ha.symm
    sorry

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    use ⟨_, (@five A _ B C _ φ f).left⟩
    ext
    exact congr_fun (@five A _ B C _ φ f).right _