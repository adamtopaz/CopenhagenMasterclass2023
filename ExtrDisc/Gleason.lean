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
  -- Checking the Chain condition
  have chain_cond : (∀ (c : Set (Set ↑(D φ f))),
      c ⊆ S →
      IsChain (fun x x_1 => x ⊆ x_1) c → ∃ lb, lb ∈ S ∧ ∀ (s : Set ↑(D φ f)), s ∈ c → lb ⊆ s) := by
    intro Ch h hCh
    let M := Set.sInter Ch
    use M
    constructor
    · constructor
      · rw [←isCompact_iff_compactSpace]
        apply @IsClosed.isCompact _ _ one
        apply isClosed_sInter
        intro N hN
        have N_comp := (h hN).1
        dsimp at N_comp
        rw [←isCompact_iff_compactSpace] at N_comp
        exact IsCompact.isClosed N_comp
      · ext x
        sorry
    · sorry


  have := zorn_superset S chain_cond
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

lemma gleason21 (X Y : Type _) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  {g : X → Y} (hg_cong : Continuous g) (hg_surj : g.Surjective) (hg : ∀ (E₀ : Set X), ¬ E₀ = ⊤ → 
  IsClosed E₀ → ¬ (g '' E₀ = ⊤)) : ∀ U : Set X, IsOpen U → (g '' U) ⊆ closure ((g '' (Uᶜ))ᶜ) :=
sorry

#check gleason21

lemma gleason22 {E₁ E₂ : Set A} (h : Disjoint E₁ E₂) : Disjoint (closure E₁) (closure E₂) := sorry

def gleason23 (E : Type _ ) [TopologicalSpace E] [T2Space E] {r : E → A} (hr : Continuous r)
  (hr_surj: r.Surjective) : 
  CompactSpace E → (∀ (E₀ : Set E), ¬ E₀ = ⊤ → IsClosed E₀ → ¬ (r '' E₀ = ⊤)) → E ≃ₜ A := by
  intros hE h_subsets
  have hr_inj : r.Injective
  · rw [Function.Injective]
    intros x y h
    by_contra h
    rcases t2_separation h with ⟨G₁, G₂, hG₁, hG₂, hxG₁, hyG₂, hG⟩
    have open1 : IsOpen (r '' (G₁ᶜ))ᶜ 
    · sorry
    have open2 : IsOpen (r '' (G₂ᶜ))ᶜ 
    · sorry
    have disj : Disjoint ((r '' (G₁ᶜ))ᶜ) ((r '' (G₂ᶜ))ᶜ)
    · sorry
    replace disj := gleason22 disj
    have oups := gleason21 E A hr hr_surj h_subsets

  let r' := Function.Embedding.equivOfSurjective ⟨r, hr_inj⟩ hr_surj
  have hr' : Continuous r'
  · sorry
  -- haveI := hE
  let j := Continuous.homeoOfEquivCompactToT2 hr'
  intros H
  exact j


def ρ : (E A B) ≃ₜ A where
  toFun := (E A B).restrict (π₁ A B)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma five : Continuous (E.restrict (π₂ φ f) ∘ ρ.invFun) ∧
  f ∘ ((E φ f).restrict (π₂ φ f) ∘ ρ.invFun) = φ := sorry

lemma gleason (A : ExtrDisc) : Projective A.compHaus where
  factors := by
    intro B C φ f _
    use ⟨_, (@five A B _ C _ f φ).left⟩
    ext
    exact congr_fun (@five A B _ C _ f φ).right _